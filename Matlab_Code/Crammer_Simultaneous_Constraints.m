function results = Crammer_Simultaneous_Constraints(varargin)
%CRAMMER_SIMULTANEOUS_CONSTRAINTS
%   Perturbation method based on Perturbation_Approach_Simultaneous_Constraints.tex.
%   Each iteration targets the current worst sidelobe and a fixed null
%   simultaneously by solving a 2x2 complex system via Cramer's rule.
%
%   Usage:
%     results = Crammer_Simultaneous_Constraints(Max_iter, eps_dB, x, y, phi_0, ...
%         'null_phi', phi_n, 'cone_rad', deg2rad(30), 'fast_peaks', true);
%
%   'final_metrics' (default false): when true, computes final_gain3D and
%   null_gain3D via full 3D pattern integration (~1.5 s extra per call).
%   When false those fields are NaN (same convention as perturb_method_v24),
%   so benchmark loops time only the algorithm itself. All cheap metrics
%   (final_gain2D, null_gain2D, skew, max sidelobe) are always computed.

    p = inputParser;
    p.FunctionName = 'Crammer_Simultaneous_Constraints';

    addRequired(p, 'Max_iter', @isnumeric);
    addRequired(p, 'eps_dB',   @isnumeric);
    addRequired(p, 'x',        @isnumeric);
    addRequired(p, 'y',        @isnumeric);
    addRequired(p, 'phi_0',    @isnumeric);

    addOptional(p, 'z', [], @isnumeric);
    addOptional(p, 'A_init', [], @isnumeric);
    addParameter(p, 'null_phi', [], @isnumeric);
    addParameter(p, 'cone_rad', [], @isnumeric);
    addParameter(p, 'fast_peaks', true, @islogical);
    addParameter(p, 'show_plots', false, @islogical);
    addParameter(p, 'show_final_plot', false, @islogical);
    addParameter(p, 'verbose', false, @islogical);
    addParameter(p, 'return_funcs', false, @islogical);
    addParameter(p, 'final_metrics', false, @islogical);
    addOptional(p, 'theta_0', pi*0.5, @isnumeric);

    parse(p, varargin{:});
    a = p.Results;

    Max_iter = a.Max_iter;
    eps_dB = a.eps_dB;
    x = a.x(:);
    y = a.y(:);
    z = a.z(:);
    phi_0 = mod(a.phi_0, 2*pi);
    theta_0 = mod(a.theta_0, 2*pi);
    null_phi = mod(a.null_phi, 2*pi);
    cone_rad = a.cone_rad;
    fast_peaks = a.fast_peaks;
    show_plots = a.show_plots;
    show_final_plot = a.show_final_plot;
    verbose = a.verbose;
    return_funcs = a.return_funcs;
    final_metrics = a.final_metrics;

    if isempty(null_phi) || any(isnan(null_phi))
        error('Crammer_Simultaneous_Constraints requires a scalar null_phi.');
    end
    if numel(null_phi) ~= 1
        error('null_phi must be a scalar angle.');
    end

    N = numel(x);
    if N < 2
        error('x,y must contain at least two elements.');
    end

    k0 = 2*pi*3e9/3e8;
    M = 1000;
    phi = linspace(0, 2*pi, M+1);
    phi(end) = [];

    K = exp(1j*k0*(x*cos(phi) + y*sin(phi)));   % NxM

    % Beam-focusing current templates from equal-magnitude steering.
    coef_phi0 = steer_vec(x, y, phi_0, k0);
    coef_null = steer_vec(x, y, null_phi, k0);

    if isempty(a.A_init)
        coef_f = coef_phi0;
    else
        A_init = a.A_init(:);
        if numel(A_init) ~= N
            error('A_init must have length N.');
        end
        coef_f = A_init .* coef_phi0;
    end

    % Enforce the requested null before the iterative loop starts.
    % psi2_n depends only on the fixed null template, so it is computed
    % once here and reused inside the loop.
    psi0_n = eval_field(coef_f, x, y, null_phi, k0);
    psi2_n = eval_field(coef_null, x, y, null_phi, k0);
    if abs(psi2_n) > 1e-14
        coef_f = coef_f - (psi0_n / psi2_n) * coef_null;
    end
    F_total = (coef_f.') * K;

    nan1 = nan(Max_iter+1, 1);
    max_sidelobe_store = nan1;
    max_side_phi_store = nan1;
    focus_value_store = nan1;
    focus_value_store_dB = nan1;
    null_value_store = nan1;
    null_value_store_dB = nan1;
    main_peakLoc_store = nan1;
    main_peakVal_store = nan1;
    directivity_metric_1_beamwidth_store = nan1;
    A1_store = nan(Max_iter, 1);
    A2_store = nan(Max_iter, 1);
    phi_s_store = nan(Max_iter, 1);

    theta_mesh = linspace(0, pi, M);    
    if return_funcs
        F_store = nan(Max_iter+1, M);
        G2D_store = nan(Max_iter+1, 1);
        G3D_store = nan(Max_iter+1, 1);
    end

    A_eff_store = cell(1, Max_iter+1);
    A_eff_store{1} = coef_f;

    tic;
    t0 = cputime; % Start CPU-clock computation timer
    iter = 0;
    record_iter(1, coef_f, F_total);

    [Slobe, phi_s, Big_phi, Big_val] = scan_peaks(F_total, phi, phi_0, cone_rad, fast_peaks);
    if ~isempty(Slobe)
        max_sidelobe_store(1) = Slobe(1);
        max_side_phi_store(1) = phi_s(1);
    end
    main_peakLoc_store(1) = Big_phi;
    main_peakVal_store(1) = Big_val;

    % Slobe/phi_s/Big_phi/Big_val always hold the scan of the CURRENT
    % F_total: the pattern is scanned exactly once per update (the old
    % code re-scanned the unchanged pattern at the top of every pass
    % and once more after the loop).
    while iter < Max_iter
        if isempty(Slobe) || Slobe(1) <= eps_dB
            break;
        end

        phi_s_cur = phi_s(1);
        coef_side = steer_vec(x, y, phi_s_cur, k0);

        psi0_s = eval_field(coef_f,    x, y, phi_s_cur, k0);
        psi0_n = eval_field(coef_f,    x, y, null_phi,  k0);
        psi1_s = eval_field(coef_side, x, y, phi_s_cur, k0);
        psi1_n = eval_field(coef_side, x, y, null_phi,  k0);
        psi2_s = eval_field(coef_null, x, y, phi_s_cur, k0);

        den = psi1_s * psi2_n - psi2_s * psi1_n;
        if abs(den) < 1e-14
            warning('Crammer_Simultaneous_Constraints:singularStep', ...
                'Singular 2x2 constraint system at iter %d; stopping early.', iter);
            break;
        end

        A1 = -((psi0_s * psi2_n) - (psi2_s * psi0_n)) / den;
        A2 = -((psi1_s * psi0_n) - (psi0_s * psi1_n)) / den;

        coef_f = coef_f + A1 * coef_side + A2 * coef_null;
        F_total = (coef_f.') * K;

        iter = iter + 1;
        A1_store(iter) = A1;
        A2_store(iter) = A2;
        phi_s_store(iter) = phi_s_cur;
        A_eff_store{iter+1} = coef_f;

        record_iter(iter+1, coef_f, F_total);

        [Slobe, phi_s, Big_phi, Big_val] = scan_peaks(F_total, phi, phi_0, cone_rad, fast_peaks);
        if ~isempty(Slobe)
            max_sidelobe_store(iter+1) = Slobe(1);
            max_side_phi_store(iter+1) = phi_s(1);
        end
        main_peakLoc_store(iter+1) = Big_phi;
        main_peakVal_store(iter+1) = Big_val;

        if verbose
            if isempty(Slobe)
                fprintf('iter=%d  phi_s=%.4f  no sidelobes remain above mask\n', iter, phi_s_cur);
            else
                fprintf('iter=%d  phi_s=%.4f  A1=%+.4g%+.4gi  A2=%+.4g%+.4gi  maxSL=%.2f dB\n', ...
                    iter, phi_s_cur, real(A1), imag(A1), real(A2), imag(A2), Slobe(1));
            end
        end

        if show_plots
            plot_pattern_v5(phi, F_total, ...
                'label', sprintf('Crammer simultaneous constraints: iter %d', iter), ...
                'phi_0', phi_0, ...
                'phi_s', phi_s, ...
                'Slobe', Slobe, ...
                'null_phi', null_phi, ...
                'show_plots', true, ...
                'iter', iter, ...
                'cone_rad', cone_rad, ...
                'Big_phi', Big_phi);
        end
    end

    % The loop exits with Slobe/phi_s/Big_phi/Big_val already holding the
    % scan of the final F_total, so no extra scan is needed here.
    Slobe_fin = Slobe;
    phi_s_fin = phi_s;
    Big_phi_final = Big_phi;
    Big_Val_final = Big_val;
    F_at_phi_0 = abs(eval_field(coef_f, x, y, phi_0, k0));
    F_at_null = abs(eval_field(coef_f, x, y, null_phi, k0));

    if show_plots || show_final_plot
        plot_pattern_v5(phi, F_total, ...
            'label', 'Final Plot: Crammer Simultaneous Constraints', ...
            'phi_0', phi_0, ...
            'phi_s', phi_s_fin, ...
            'Slobe', Slobe_fin, ...
            'null_phi', null_phi, ...
            'show_plots', true, ...
            'iter', iter, ...
            'cone_rad', cone_rad, ...
            'Big_phi', Big_phi_final);
    end

    results.method = 'Crammer_Simultaneous_Constraints';
    results.fast_peaks = fast_peaks;
    results.final_iteration = iter;
    results.final_epoch = iter;
    results.total_time = toc;
    results.elapsed_cpu_time = cputime - t0;
    results.focus_angle = phi_0;
    results.focus_angle_deg = round(rad2deg(phi_0));
    results.null_angle = null_phi;
    results.null_angle_deg = round(rad2deg(null_phi));
    results.cone_rad = cone_rad;

    results.final_function = F_total;
    results.F_at_phi_0 = F_at_phi_0;
    results.F_at_null = F_at_null;
    results.A_eff = coef_f;
    results.A_eff_store = A_eff_store(1:iter+1);
    results.x_pos = x;
    results.y_pos = y;

    results.max_sidelobe_store = max_sidelobe_store;
    results.max_side_phi_store = max_side_phi_store;
    results.focus_value_store = abs(focus_value_store);
    results.focus_value_store_dB = focus_value_store_dB;
    results.null_value_store = abs(null_value_store);
    results.null_value_store_dB = null_value_store_dB;
    results.main_peakLoc_store = main_peakLoc_store;
    results.main_peakVal_store = main_peakVal_store;
    results.directivity_metric_1_beamwidth_store = directivity_metric_1_beamwidth_store;

    results.A1_store = A1_store;
    results.A2_store = A2_store;
    results.phi_s_store = phi_s_store;
    results.phi_s_fin = phi_s_fin;
    results.Big_phi_final = Big_phi_final;
    results.Big_Val_final = Big_Val_final;
    results.initial_template_phi0 = coef_phi0;
    results.null_template = coef_null;

    %% ---- Final metrics: gain, main-beam skew, max sidelobe ----
    % Same set of fields perturb_method_v25 returns, computed with this
    % file's helpers (local_gain2D, local_gain3D, scan_peaks). Crammer
    % always has a null direction, so null_gain2D is always populated
    % (no use_null branch); the 3D gains are gated by 'final_metrics'.

    % Focus/null-direction 2D gains: cheap (trapz over the existing
    % pattern), always computed.
    results.final_gain2D = local_gain2D(F_total, phi, phi_0);
    results.null_gain2D = local_gain2D(F_total, phi, null_phi);

    % 3D gains require integrating the full 3D pattern (M theta-cuts of
    % an NxM field each) — by far the most expensive step in this file,
    % so they are only computed on request ('final_metrics', true).
    if final_metrics
        results.final_gain3D = local_gain3D(phi, theta_mesh, coef_f, ...
                                            x, y, z, k0, phi_0, theta_0);
        results.null_gain3D = local_gain3D(phi, theta_mesh, coef_f, ...
                                           x, y, z, k0, null_phi, theta_0);
    else
        results.final_gain3D = NaN;
        results.null_gain3D = NaN;
    end

    % Main-beam skew: angular distance between phi_0 and the actual peak
    % of the main beam in the FINAL pattern. Big_phi_final already came
    % out of scan_peaks above, applied to the post-iteration F_total.
    % atan2(sin(d), cos(d)) wraps any angle into (-pi, pi], so abs() of
    % that gives the wrap-aware unsigned distance.
    delta = phi_0 - Big_phi_final;
    results.main_beam_angle_final           = Big_phi_final;             % rad
    results.main_beam_skew_final_signed     = atan2(sin(delta), cos(delta));
    results.main_beam_skew_final_signed_deg = rad2deg(results.main_beam_skew_final_signed);
    results.main_beam_skew_final            = abs(results.main_beam_skew_final_signed);
    results.main_beam_skew_final_deg        = rad2deg(results.main_beam_skew_final);

    % Final max sidelobe. Slobe_fin is already scan_peaks's sorted-
    % descending dB list of post-cone sidelobes from the FINAL F_total,
    % so Slobe_fin(1) is the answer. The -Inf vs NaN distinction matches
    % perturb_method_v25's convention: -Inf means "main beam found, no
    % sidelobes survived the cone filter"; NaN means "no peaks at all."
    if isempty(phi_s_fin)
        % scan_peaks returned no peaks at all (degenerate pattern)
        % OR returned only the main beam (no surviving sidelobes after cone).
        % Use Big_Val_final's presence as the discriminator: scan_peaks
        % sets Big_phi to phi_0 and Big_val to interp1(...) in the
        % no-peaks case, but in the no-surviving-sidelobes case the main
        % beam was found.
        results.final_max_sidelobe_dB      = -Inf;   % conservative
        results.final_max_sidelobe_phi     = NaN;
        results.final_max_sidelobe_phi_deg = NaN;
    else
        results.final_max_sidelobe_dB      = Slobe_fin(1);
        results.final_max_sidelobe_phi     = phi_s_fin(1);
        results.final_max_sidelobe_phi_deg = rad2deg(phi_s_fin(1));
    end


    if return_funcs
        results.F_store = F_store;
        results.G2D_store = G2D_store;
        results.G3D_store = G3D_store;
    end

    function record_iter(idx, coef_now, F_now)
        Fmag = abs(F_now);
        Fmax = max(Fmag);
        F0 = eval_field(coef_now, x, y, phi_0, k0);
        Fn = eval_field(coef_now, x, y, null_phi, k0);

        focus_value_store(idx) = F0;
        null_value_store(idx) = Fn;
        focus_value_store_dB(idx) = 10*log10(abs(F0).^2 / Fmax.^2);
        null_value_store_dB(idx) = 10*log10(max(abs(Fn).^2, eps) / Fmax.^2);

        if return_funcs
            bw = directivity_met_v2(phi, F_now, phi_0);
            directivity_metric_1_beamwidth_store(idx) = bw.beamwidth;
            F_store(idx, :) = F_now;
            G2D_store(idx) = local_gain2D(F_now, phi, phi_0);
            G3D_store(idx) = local_gain3D(phi, theta_mesh, coef_now, x, y, z, k0, phi_0, theta_0);
        end
    end
end


function c = steer_vec(x, y, phi0, k0)
    c = exp(-1j * k0 * (x*cos(phi0) + y*sin(phi0)));
end


function F = eval_field(coef, x, y, phi0, k0)
    F = coef.' * exp(1j * k0 * (x*cos(phi0) + y*sin(phi0)));
end


function [Slobe, phi_s, Big_phi, Big_val] = scan_peaks(F_total, phi, phi_0, cone_rad, fast_peaks)
    Fmag = abs(F_total);
    if fast_peaks
        [peakVals, peakLocs] = findpeaks_fast(Fmag, phi);
    else
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
    end

    if isempty(peakVals)
        Slobe = [];
        phi_s = [];
        Big_phi = phi_0;
        Big_val = abs(interp1(phi, Fmag, phi_0, 'linear', 'extrap'));
        return;
    end

    d_main = abs(atan2(sin(peakLocs - phi_0), cos(peakLocs - phi_0)));
    [~, imain] = min(d_main);
    Big_phi = peakLocs(imain);
    Big_val = peakVals(imain);
    peakVals(imain) = [];
    peakLocs(imain) = [];

    if ~isempty(cone_rad) && ~isempty(peakLocs)
        d = mod(peakLocs - phi_0 + pi, 2*pi) - pi;
        keep = abs(d) > cone_rad;
        peakVals = peakVals(keep);
        peakLocs = peakLocs(keep);
    end

    if isempty(peakVals)
        Slobe = [];
        phi_s = [];
        return;
    end

    peakVals_dB = 10*log10((peakVals.^2) / max(Fmag).^2);
    [Slobe, ix] = sort(peakVals_dB, 'descend');
    phi_s = peakLocs(ix);
end


function G = local_gain2D(F_total, phi, phi_0)
    phi = phi(:).';
    I = trapz(phi, abs(F_total).^2, 2);
    F0 = interp1(phi, F_total.', phi_0, 'linear', 'extrap').';
    G = 10*log10((abs(F0).^2 * 4*pi) ./ I);
end


function G = local_gain3D(phi, theta_mesh, A, x, y, z, k0, phi_0, theta_0)
    if isempty(z)
        z = zeros(size(A));
    end
    A = A(:);
    x = x(:);
    y = y(:);
    z = z(:);
    phi = phi(:).';
    theta = theta_mesh(:);
    L = numel(theta);
    Mp = numel(phi);
    F = zeros(L, Mp);
    % In-plane phase matrix is theta-independent: hoist it out of the loop.
    B = x*cos(phi) + y*sin(phi);    % NxMp
    has_z = any(z ~= 0);
    for li = 1:L
        sT = sin(theta(li));
        cT = cos(theta(li));
        if has_z
            ph = k0 * (sT*B + z*cT);
        else
            ph = (k0*sT) * B;
        end
        E = cos((pi/2) * cT) / sT;
        if ~isfinite(E)
            E = 0;
        end
        F(li, :) = (A.') * exp(1j * ph) * E;
    end
    Pw = abs(F).^2 .* sin(theta);
    Itot = trapz(theta, trapz(phi, Pw, 2));
    F0 = interp2(phi, theta, F, phi_0, theta_0, 'linear', 0);
    G = 10*log10((abs(F0)^2 * 4*pi) / Itot);
end
