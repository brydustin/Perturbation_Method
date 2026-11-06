%% Perturbative Sidelobe-Reduction Method
%
% Implements three modes:
%   (1) Ordinary perturbative method  (default)
%   (2) Constrained perturbative method  ('constrained', true)
%       — beam value at phi_0 is preserved exactly at every step.
%   (3) Simultaneous-constraints method  ('simultaneous', true, 'phi_null', phi_n)
%       — reduces the largest sidelobe AND enforces a null at phi_n simultaneously
%         each iteration by solving two constraint equations (Cramer's rule).
%
% Usage:
%   results = perturb_method(Max_iter, eps_dB, x, y, phi_0)
%   results = perturb_method(Max_iter, eps_dB, x, y, phi_0, Name, Value, ...)
%
% Required inputs:
%   Max_iter   - maximum number of outer (while-loop) epochs
%   eps_dB     - sidelobe threshold in dB (e.g. -20)
%   x, y       - Nx1 element position vectors (metres)
%   phi_0      - beam steering direction (radians)
%
% Optional name-value inputs:
%   z            - Nx1 z-coordinates for 3-D gain (default: zeros)
%   A_init       - Nx1 initial amplitude vector (default: ones)
%   theta_0      - elevation angle for 3-D gain (default: pi/2)
%   constrained  - logical; use beam-preserving constrained method (default: false)
%   simultaneous - logical; use simultaneous sidelobe+null method (default: false)
%   phi_null     - null angle (radians); required when simultaneous=true
%   full_loop    - logical; correct all sidelobes per epoch, not just the worst (default: false)
%   cone_rad     - exclude sidelobes within cone_rad radians of phi_0 (default: [])
%   show_plots   - logical; show pattern at every epoch (default: false)
%   show_final   - logical; show final pattern only (default: false)
%   return_funcs - logical; store pattern at every epoch (default: false)
%   verbose      - logical; print per-epoch diagnostics (default: false)
%
% Output: results struct (see end of file for full field list)
%
% Dependencies: plot_pattern_v5.m, findpeaks_circular.m, directivity_met_v2.m
%
function results = perturb_method(Max_iter, eps_dB, x, y, phi_0, varargin)

    %% ---- Parse inputs -------------------------------------------------------
    p = inputParser;
    p.FunctionName = 'perturb_method';

    addRequired(p, 'Max_iter',  @(v) isnumeric(v) && isscalar(v) && v > 0);
    addRequired(p, 'eps_dB',    @(v) isnumeric(v) && isscalar(v));
    addRequired(p, 'x',         @isnumeric);
    addRequired(p, 'y',         @isnumeric);
    addRequired(p, 'phi_0',     @(v) isnumeric(v) && isscalar(v));

    addParameter(p, 'z',            [],      @isnumeric);
    addParameter(p, 'A_init',       [],      @isnumeric);
    addParameter(p, 'theta_0',      pi/2,    @(v) isnumeric(v) && isscalar(v));
    addParameter(p, 'constrained',  false,   @(v) islogical(v) || ismember(v,[0 1]));
    addParameter(p, 'simultaneous', false,   @(v) islogical(v) || ismember(v,[0 1]));
    addParameter(p, 'phi_null',     NaN,     @(v) isnumeric(v) && isscalar(v));
    addParameter(p, 'full_loop',    false,   @(v) islogical(v) || ismember(v,[0 1]));
    addParameter(p, 'cone_rad',     [],      @isnumeric);
    addParameter(p, 'show_plots',   false,   @(v) islogical(v) || ismember(v,[0 1]));
    addParameter(p, 'show_final',   false,   @(v) islogical(v) || ismember(v,[0 1]));
    addParameter(p, 'return_funcs', false,   @(v) islogical(v) || ismember(v,[0 1]));
    addParameter(p, 'verbose',      false,   @(v) islogical(v) || ismember(v,[0 1]));

    parse(p, Max_iter, eps_dB, x, y, phi_0, varargin{:});
    r = p.Results;

    % Unpack
    Max_iter     = r.Max_iter;
    eps_dB       = r.eps_dB;
    x            = r.x(:);
    y            = r.y(:);
    z            = r.z;
    phi_0        = mod(r.phi_0, 2*pi);
    theta_0      = mod(r.theta_0, 2*pi);
    A_init       = r.A_init;
    use_constrained  = logical(r.constrained);
    use_simultaneous = logical(r.simultaneous);
    phi_null         = r.phi_null;
    full_loop        = logical(r.full_loop);
    cone_rad     = r.cone_rad;
    show_plots   = logical(r.show_plots);
    show_final   = logical(r.show_final) || show_plots;
    return_funcs = logical(r.return_funcs);
    verbose      = logical(r.verbose);

    if use_simultaneous && use_constrained
        error('perturb_method: ''simultaneous'' and ''constrained'' are mutually exclusive.');
    end
    if use_simultaneous && isnan(phi_null)
        error('perturb_method: ''phi_null'' must be specified when using simultaneous method.');
    end
    if use_simultaneous
        phi_null = mod(phi_null, 2*pi);
    end

    N = numel(x);
    if N < 2
        error('perturb_method: need at least 2 elements.');
    end
    if ~isempty(z),     z = z(:);     else, z = zeros(N,1); end
    if ~isempty(A_init)
        A_init = A_init(:);
        if numel(A_init) ~= N
            error('perturb_method: A_init must have length N = %d.', N);
        end
    else
        A_init = ones(N,1);
    end

    %% ---- RF constants -------------------------------------------------------
    freq   = 3e9;
    k0     = 2*pi*freq / 3e8;

    %% ---- Evaluation grid ----------------------------------------------------
    M_grid    = 1000;
    phi       = linspace(0, 2*pi, M_grid + 1);
    phi(end)  = [];                        % remove 2*pi duplicate
    theta_vec = linspace(0, pi, M_grid);   % elevation grid for 3-D gain

    %% ---- Initial steering and amplitudes ------------------------------------
    delta0 = -k0 * (x*cos(phi_0) + y*sin(phi_0));
    A0     = A_init;

    %% ---- Pre-allocate storage -----------------------------------------------
    max_sidelobe_store = nan(Max_iter+1, 1);
    max_side_phi_store = nan(Max_iter+1, 1);
    main_peakLoc_store = nan(Max_iter+1, 1);
    main_peakVal_store = nan(Max_iter+1, 1);
    focus_val_store    = nan(Max_iter+1, 1);
    focus_dB_store     = nan(Max_iter+1, 1);
    beamwidth_store    = nan(Max_iter+1, 1);
    G2D_store          = nan(Max_iter+1, 1);
    G3D_store          = nan(Max_iter+1, 1);

    A_store     = {A0};
    delta_store = {delta0};
    phi_store   = phi_0;
    A_eff_store = {A0 .* exp(1j * delta0)};

    if return_funcs
        F_store = nan(Max_iter+1, M_grid);
    end

    %% ---- Step 3: Compute initial field --------------------------------------
    F_total = arrayFactor2D(phi, A0, x, y, delta0, k0);

    if return_funcs
        F_store(1,:) = F_total(:).';
        G2D_store(1) = gain2D(F_total, phi, phi_0, k0);
        G3D_store(1) = gain3D(phi, theta_vec, A_eff_store{1}, x, y, z, [], k0, phi_0, theta_0);
    end

    %% ---- Constrained method: fix beam value B = f_0(phi_0) -----------------
    if use_constrained
        % B = f_0(phi_0) is held constant throughout
        B = interp1(phi, F_total, phi_0, 'linear', 'extrap');
        % Beam kernel K_{phi_0}(phi) = arrayFactor2D with unit amplitudes steered to phi_0
        delta_beam   = -k0 * (x*cos(phi_0) + y*sin(phi_0));
        K_beam       = arrayFactor2D(phi, ones(N,1), x, y, delta_beam, k0);  % 1xM
        % g_0 = f_0 - (B/N)*K_beam
        g_total      = F_total - (B/N) * K_beam;
    end

    %% ---- Steps 4–7: initial sidelobe identification -------------------------
    [Slobe, phi_s, main_info] = findSidelobes(F_total, phi, phi_0, eps_dB, cone_rad);

    main_peakLoc_store(1) = main_info.loc;
    main_peakVal_store(1) = main_info.val;
    focus_val_store(1)    = main_info.focus_val;
    focus_dB_store(1)     = main_info.focus_dB;
    bw = directivity_met_v2(phi, F_total, phi_0);
    beamwidth_store(1)    = bw.beamwidth;
    if isempty(Slobe)
        max_sidelobe_store(1) = NaN;
        max_side_phi_store(1) = NaN;
    else
        max_sidelobe_store(1) = Slobe(1);
        max_side_phi_store(1) = phi_s(1);
    end

    if show_plots
        plot_pattern_v5(phi, F_total, 'label', "Initial Pattern", ...
            'phi_0', phi_0, 'phi_s', phi_s, 'Slobe', Slobe, ...
            'show_plots', true, 'iter', 0);
    end

    m    = numel(Slobe);
    iter = 0;

    if verbose
        fprintf('[Init] %d sidelobes above %.1f dB\n', m, eps_dB);
    end

    %% ---- Main loop (Steps 8–16) --------------------------------------------
    tic;

    while m > 0 && iter < Max_iter

        m_epoch = 1;
        if full_loop, m_epoch = m; end

        for t = 1:m_epoch

            alpha_s     = phi_s(t);
            delta_corr  = -k0 * (x*cos(alpha_s) + y*sin(alpha_s));
            F_at_alpha  = interp1(phi, F_total, alpha_s, 'linear', 'extrap');

            if use_constrained
                % ------- Constrained correction --------------------------------
                % K_{alpha_s}(phi) — reproducing kernel aimed at alpha_s
                K_alpha = arrayFactor2D(phi, ones(N,1), x, y, delta_corr, k0);

                % K_{alpha_s}(phi_0): scalar coupling to beam direction
                K_alpha_at_phi0 = interp1(phi, K_alpha, phi_0, 'linear', 'extrap');

                % Projected (constrained) kernel: K_tilde = K_alpha - (K_alpha(phi_0)/N)*K_beam
                L_tilde     = N - abs(K_alpha_at_phi0)^2 / N;   % = ||K_tilde||^2
                K_tilde     = K_alpha - (K_alpha_at_phi0 / N) * K_beam;

                % g_n(alpha_s) = F_total(alpha_s) - (B/N)*K_beam(alpha_s)
                K_beam_at_alpha = interp1(phi, K_beam, alpha_s, 'linear', 'extrap');
                g_at_alpha      = F_at_alpha - (B/N) * K_beam_at_alpha;

                % Constrained update: g_{n+1} = g_n - (g_n(alpha)/L_tilde)*K_tilde
                dF       = -(g_at_alpha / L_tilde) * K_tilde;
                F_total  = F_total + dF;
                g_total  = g_total + dF;   % dF has zero component at phi_0

                % Effective amplitude update (for gain calculations)
                % dF = sum_j A_tilde_eff(j) * exp(ik0*(xj*cos(phi)+yj*sin(phi)))
                % where A_tilde_eff(j) = -(g_at_alpha/L_tilde)*
                %                         [exp(i*delta_corr(j)) - (K_alpha_at_phi0/N)*exp(i*delta_beam(j))]
                coeff          = -g_at_alpha / L_tilde;
                dA_eff         = coeff * (exp(1j*delta_corr) - (K_alpha_at_phi0/N)*exp(1j*delta_beam));
                A_eff_store{end+1} = A_eff_store{end} + dA_eff;

                % Store correction components
                A_store{end+1}     = coeff * (ones(N,1) - (K_alpha_at_phi0/N)*ones(N,1));
                delta_store{end+1} = delta_corr;   % approximate; effective A encodes full correction
                phi_store(end+1)   = alpha_s;

            elseif use_simultaneous
                % ------- Simultaneous constraints correction -------------------
                % psi_0 = F_total  (current pattern)
                % psi_1 = beam steered to phi_s  (largest sidelobe angle)
                % psi_2 = beam steered to phi_n  (desired null angle)
                % Constraint eqs force total pattern to zero at both phi_s and phi_n.
                delta_s = -k0 * (x*cos(alpha_s)  + y*sin(alpha_s));
                delta_n = -k0 * (x*cos(phi_null) + y*sin(phi_null));

                psi_1 = arrayFactor2D(phi, ones(N,1), x, y, delta_s, k0);
                psi_2 = arrayFactor2D(phi, ones(N,1), x, y, delta_n, k0);

                % Sample all three patterns at phi_s and phi_null
                psi0_s = interp1(phi, F_total, alpha_s,  'linear', 'extrap');
                psi0_n = interp1(phi, F_total, phi_null, 'linear', 'extrap');
                psi1_s = interp1(phi, psi_1,   alpha_s,  'linear', 'extrap');
                psi1_n = interp1(phi, psi_1,   phi_null, 'linear', 'extrap');
                psi2_s = interp1(phi, psi_2,   alpha_s,  'linear', 'extrap');
                psi2_n = interp1(phi, psi_2,   phi_null, 'linear', 'extrap');

                % Cramer's rule — denominator det
                D = psi1_s*psi2_n - psi2_s*psi1_n;

                if abs(D) < 1e-12
                    % Degenerate: fall back to ordinary single-sidelobe correction
                    A1 = -psi0_s / N;
                    A2 = 0;
                else
                    A1 = -(psi0_s*psi2_n - psi2_s*psi0_n) / D;
                    A2 = -(psi1_s*psi0_n - psi0_s*psi1_n) / D;
                end

                dF      = A1*psi_1 + A2*psi_2;
                F_total = F_total + dF;

                % Effective current update: dA_eff(n) = A1*exp(j*delta_s(n)) + A2*exp(j*delta_n(n))
                dA_eff             = A1*exp(1j*delta_s) + A2*exp(1j*delta_n);
                A_eff_store{end+1} = A_eff_store{end} + dA_eff;

                % Store both components so A_eff reconstruction loop stays valid
                A_store{end+1}     = A1 * ones(N,1);
                delta_store{end+1} = delta_s;
                A_store{end+1}     = A2 * ones(N,1);
                delta_store{end+1} = delta_n;
                phi_store(end+1)   = alpha_s;
                phi_store(end+1)   = phi_null;

            else
                % ------- Ordinary correction -----------------------------------
                A_corr_scalar  = -F_at_alpha / N;
                A_corr_vec     = A_corr_scalar * ones(N,1);
                dF             = arrayFactor2D(phi, A_corr_vec, x, y, delta_corr, k0);
                F_total        = F_total + dF;

                A_store{end+1}     = A_corr_vec;
                delta_store{end+1} = delta_corr;
                phi_store(end+1)   = alpha_s;
                A_eff_store{end+1} = A_eff_store{end} + A_corr_vec .* exp(1j*delta_corr);
            end

        end % for t

        iter = iter + 1;

        % --- Gain tracking (only if return_funcs requested) ---
        if return_funcs
            F_store(iter+1, :) = F_total(:).';
            G2D_store(iter+1)  = gain2D(F_total, phi, phi_0, k0);
            G3D_store(iter+1)  = gain3D(phi, theta_vec, A_eff_store{end}, x, y, z, [], k0, phi_0, theta_0);
        end

        % --- Re-identify sidelobes ---
        [Slobe, phi_s, main_info] = findSidelobes(F_total, phi, phi_0, eps_dB, cone_rad);

        main_peakLoc_store(iter+1) = main_info.loc;
        main_peakVal_store(iter+1) = main_info.val;
        focus_val_store(iter+1)    = main_info.focus_val;
        focus_dB_store(iter+1)     = main_info.focus_dB;
        bw = directivity_met_v2(phi, F_total, phi_0);
        beamwidth_store(iter+1)    = bw.beamwidth;
        if isempty(Slobe)
            max_sidelobe_store(iter+1) = NaN;
            max_side_phi_store(iter+1) = NaN;
        else
            max_sidelobe_store(iter+1) = Slobe(1);
            max_side_phi_store(iter+1) = phi_s(1);
        end

        m = numel(Slobe);

        if verbose
            fprintf('[Epoch %3d] %d sidelobes above %.1f dB | max = %.2f dB\n', ...
                iter, m, eps_dB, max_sidelobe_store(iter+1));
        end

        if show_plots
            lbl = sprintf("Epoch %d", iter);
            plot_pattern_v5(phi, F_total, 'label', lbl, ...
                'phi_0', phi_0, 'phi_s', phi_s, 'Slobe', Slobe, ...
                'show_plots', true, 'iter', iter, ...
                'Big_phi', main_peakLoc_store(iter+1));
        end

    end % while

    total_time = toc;

    %% ---- Final peak analysis ------------------------------------------------
    Fmag = abs(F_total);
    [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
    [~, mainIdx] = min(angDiff(peakLocs, phi_0));
    Big_Val_final = peakVals(mainIdx);
    Big_phi_final = peakLocs(mainIdx);
    peakVals(mainIdx) = [];
    peakLocs(mainIdx) = [];
    if isempty(peakVals)
        Slobe_final   = [];
        phi_s_final   = [];
    else
        peakVals_dB = 10*log10(peakVals.^2 / max(Fmag)^2);
        [Slobe_final, sIdx] = sort(peakVals_dB, 'descend');
        phi_s_final = peakLocs(sIdx);
    end

    %% ---- Effective amplitudes (full sum) ------------------------------------
    A_eff = zeros(N,1);
    for k = 1:numel(A_store)
        A_eff = A_eff + A_store{k} .* exp(1j * delta_store{k});
    end

    %% ---- Final plot ---------------------------------------------------------
    if show_final
        lbl = "Final Pattern";
        if use_constrained,  lbl = "Final Pattern (Constrained Method)";    end
        if use_simultaneous, lbl = "Final Pattern (Simultaneous Constraints)"; end
        plot_pattern_v5(phi, F_total, 'label', lbl, ...
            'phi_0', phi_0, 'phi_s', phi_s_final, 'Slobe', Slobe_final, ...
            'show_plots', true, 'iter', iter, ...
            'cone_rad', cone_rad, 'Big_phi', Big_phi_final);
    end

    %% ---- Assemble output ----------------------------------------------------
    if use_constrained
        results.method = "constrained";
    elseif use_simultaneous
        results.method = "simultaneous";
    else
        results.method = "ordinary";
    end
    results.final_epoch           = iter;
    results.total_time            = total_time;
    results.converged             = (m == 0);

    results.focus_angle           = phi_0;
    results.focus_angle_deg       = rad2deg(phi_0);
    results.cone_rad              = cone_rad;
    if use_simultaneous
        results.null_angle     = phi_null;
        results.null_angle_deg = rad2deg(phi_null);
        results.null_val_final = abs(interp1(phi, F_total, phi_null, 'linear', 'extrap'));
    end

    results.max_sidelobe_store    = max_sidelobe_store(1:iter+1);
    results.max_side_phi_store    = max_side_phi_store(1:iter+1);
    results.main_peakLoc_store    = main_peakLoc_store(1:iter+1);
    results.main_peakVal_store    = main_peakVal_store(1:iter+1);
    results.focus_val_store       = abs(focus_val_store(1:iter+1));
    results.focus_dB_store        = abs(focus_dB_store(1:iter+1));
    results.beamwidth_store       = beamwidth_store(1:iter+1);

    results.final_function        = F_total;
    results.final_sidelobes_dB    = Slobe_final;
    results.final_sidelobe_angles = phi_s_final;
    results.Big_Val_final         = Big_Val_final;
    results.Big_phi_final         = Big_phi_final;
    results.F_at_phi_0            = abs(interp1(phi, F_total, phi_0, 'linear', 'extrap'));

    results.A_store               = A_store;
    results.delta_store           = delta_store;
    results.phi_store             = phi_store;
    results.A_eff_store           = A_eff_store;
    results.A_eff                 = A_eff;
    results.x_pos                 = x;
    results.y_pos                 = y;

    results.final_gain2D          = gain2D(F_total, phi, phi_0, k0);
    results.final_gain3D          = gain3D(phi, theta_vec, A_eff, x, y, z, [], k0, phi_0, theta_0);

    if return_funcs
        results.F_store   = F_store(1:iter+1, :);
        results.G2D_store = G2D_store(1:iter+1);
        results.G3D_store = G3D_store(1:iter+1);
    end

    if use_constrained
        results.B       = B;       % preserved beam value f_0(phi_0)
        results.g_final = g_total; % final g_n = f_n - (B/N)*K_{phi_0}

        % BDC coupling parameter beta = max_{alpha visited} |K_alpha(phi_0)|
        % Approximated over all sidelobe angles targeted by the algorithm.
        alpha_visited = phi_store(:);
        K_at_phi0 = zeros(numel(alpha_visited), 1);
        for kk = 1:numel(alpha_visited)
            d_a = -k0 * (x*cos(alpha_visited(kk)) + y*sin(alpha_visited(kk)));
            Ka  = arrayFactor2D(phi, ones(N,1), x, y, d_a, k0);
            K_at_phi0(kk) = abs(interp1(phi, Ka, phi_0, 'linear', 'extrap'));
        end
        beta          = max(K_at_phi0);
        results.beta           = beta;         % max coupling |K_alpha(phi_0)|
        results.beta_over_L    = beta / N;     % termination criterion: need <= 10^(eps_dB/20)
        results.BDC_satisfied  = (beta < N);   % Beam-Decoupling Condition
        results.terminates_iff = 10^(eps_dB/20); % threshold: beta/L must be <= this
    end

    %% ========================================================================
    %% Local functions
    %% ========================================================================

    % -------------------------------------------------------------------------
    function F = arrayFactor2D(phi_v, A_v, x_v, y_v, delta_v, k_v)
    % 2-D array factor. Returns 1xM complex row vector.
        A_v     = A_v(:);
        x_v     = x_v(:);
        y_v     = y_v(:);
        if isempty(delta_v)
            delta_v = zeros(numel(A_v), 1);
        else
            delta_v = delta_v(:);
        end
        phi_v = phi_v(:).';                      % 1xM
        phase = k_v*(x_v*cos(phi_v) + y_v*sin(phi_v)) + delta_v;   % NxM
        F = A_v.' * exp(1j * phase);             % 1xM
    end

    % -------------------------------------------------------------------------
    function F = arrayFactor3D(phi_v, theta_v, A_v, x_v, y_v, z_v, delta_v, k_v)
    % 3-D array factor with dipole element pattern. Returns LxM matrix.
        A_v = A_v(:); x_v = x_v(:); y_v = y_v(:); z_v = z_v(:);
        if isempty(delta_v), delta_v = zeros(numel(A_v),1); else, delta_v = delta_v(:); end
        phi_v   = phi_v(:).';           % 1xM
        theta_v = theta_v(:).';         % 1xL
        [PHI, THETA] = meshgrid(phi_v, theta_v);   % LxM

        xr = reshape(x_v,     [],1,1);
        yr = reshape(y_v,     [],1,1);
        zr = reshape(z_v,     [],1,1);
        dr = reshape(delta_v, [],1,1);
        TH = reshape(THETA, 1, size(THETA,1), size(THETA,2));
        PH = reshape(PHI,   1, size(PHI,1),   size(PHI,2));

        phase = k_v*(xr.*sin(TH).*cos(PH) + yr.*sin(TH).*sin(PH) + zr.*cos(TH)) + dr;
        E = cos((pi/2)*cos(TH)) ./ sin(TH);
        E(~isfinite(E)) = 0;

        Ar = reshape(A_v, [],1,1);
        F  = squeeze(sum(Ar .* E .* exp(1j*phase), 1));
    end

    % -------------------------------------------------------------------------
    function G = gain2D(F_v, phi_v, phi0, k_v) %#ok<INUSD>
    % 2-D gain (dBi) in direction phi0.
        phi_v = phi_v(:).';
        I     = trapz(phi_v, abs(F_v).^2);
        F0    = interp1(phi_v, F_v(:).', phi0, 'linear', 'extrap');
        G     = 10*log10(abs(F0)^2 * 4*pi / I);
    end

    % -------------------------------------------------------------------------
    function G = gain3D(phi_v, theta_v, A_v, x_v, y_v, z_v, delta_v, k_v, phi0, theta0)
    % 3-D gain (dBi) in direction (phi0, theta0).
        F3  = arrayFactor3D(phi_v, theta_v, A_v, x_v, y_v, z_v, delta_v, k_v);
        P   = abs(F3).^2;
        P(~isfinite(P)) = 0;
        I_phi  = trapz(phi_v(:).', P .* sin(theta_v(:)), 2);
        I      = trapz(theta_v(:), I_phi);
        F0     = interp2(phi_v(:).', theta_v(:), F3, phi0, theta0, 'linear');
        G      = 10*log10(abs(F0)^2 * 4*pi / I);
    end

    % -------------------------------------------------------------------------
    function d = angDiff(a, b)
    % Absolute circular angular distance in [0, pi].
        d = abs(atan2(sin(a - b), cos(a - b)));
        d(d < 1e-12) = 0;
    end

    % -------------------------------------------------------------------------
    function [Slobe, phi_s, minfo] = findSidelobes(F_v, phi_v, phi0, thresh_dB, c_rad)
    % Detect sidelobes above thresh_dB, excluding the main beam and optionally
    % excluding directions within c_rad of phi0. Returns sorted descending.
        Fmag = abs(F_v);
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi_v);

        if isempty(peakVals)
            Slobe = []; phi_s = [];
            minfo = struct('loc', NaN, 'val', NaN, 'focus_val', NaN, 'focus_dB', NaN);
            return;
        end

        peakLocs = mod(peakLocs, 2*pi);
        [~, mainIdx] = min(angDiff(peakLocs, phi0));

        minfo.loc       = peakLocs(mainIdx);
        minfo.val       = peakVals(mainIdx);
        minfo.focus_val = interp1(phi_v, F_v, phi0, 'linear', 'extrap');
        minfo.focus_dB  = 10*log10(abs(minfo.focus_val)^2 / max(Fmag)^2);

        peakVals(mainIdx) = [];
        peakLocs(mainIdx) = [];

        if isempty(peakVals)
            Slobe = []; phi_s = []; return;
        end

        peakVals_dB = 10*log10(peakVals.^2 / max(Fmag)^2);
        mask = peakVals_dB > thresh_dB;

        if ~isempty(c_rad)
            d   = mod(peakLocs - phi0 + pi, 2*pi) - pi;
            mask = mask & (abs(d) > c_rad);
        end

        Slobe = peakVals_dB(mask);
        phi_s = peakLocs(mask);

        [Slobe, sIdx] = sort(Slobe, 'descend');
        phi_s = phi_s(sIdx);
    end

end
