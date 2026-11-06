function res = processing_error_analysis(varargin)
%PROCESSING_ERROR_ANALYSIS  Monte Carlo robustness sweep against polar-form
%   perturbations of the optimized basis-function coefficients.
%
%   Procedure:
%     1. Run the selected perturbation method on the ideal layout to obtain
%        the optimized coefficients A_eff.
%     2. For each sigma in sigma_list, run n_trials independent Monte
%        Carlo realizations:
%             A_eff = mag .* exp(1j * phase)
%        dist == "normal"  (additive Gaussian, std = sigma):
%             if perturb_component == "magnitude"
%                 mag_noisy   = max(mag + sigma * randn(N,1), 0)
%                 phase_noisy = phase
%             elseif perturb_component == "phase"
%                 mag_noisy   = mag
%                 phase_noisy = phase + sigma * randn(N,1)
%             end
%        dist == "uniform" (multiplicative, e ~ Uniform[-sigma, sigma],
%                           sigma plays the role of the half-width epsilon):
%             if perturb_component == "magnitude"
%                 mag_noisy   = max(mag .* (1 + e), 0)     % A -> A(1+e)
%                 phase_noisy = phase
%             elseif perturb_component == "phase"
%                 mag_noisy   = mag
%                 phase_noisy = phase .* (1 + e)           % theta -> theta(1+e)
%             end
%             A_noisy = mag_noisy .* exp(1j * phase_noisy)
%             F       = A_noisy.' * K            % full pattern over phi mesh
%             ws(t)   = worst sidelobe (dB rel own peak), main beam excluded
%        Aggregate to mean(ws), std(ws), Pr(ws > threshold) over trials.
%     3. Report sigma_break = smallest sigma at which the *mean* worst
%        sidelobe exceeds threshold_dB ("breaks on average"), via linear
%        interpolation between bracketing sweep points.
%
%   Name-value parameters:
%     N            : 9            ring element count (odd, >= 3)
%     d_ideal      : 0.04880      ring spacing
%     phi_0        : 0            steered direction (rad)
%     null_phi     : []           optional null direction (rad, v24/v23 only)
%     Max_iter     : 60           v24 iteration budget
%     eps_dB       : -20          v24 sidelobe target
%     threshold_dB : -20          break threshold for worst sidelobe
%     null_threshold_dB : -40     break threshold for null level
%     method       : 'v24'        'v24' or 'constrained'
%     cone_rad     : []           constrained-method cone half-angle
%     max_outer_passes : 50       constrained-method outer-pass cap
%     sigma_list   : logspace(-3,1,41)  noise std sweep
%     n_trials     : 300          MC realizations per sigma
%     perturb_component : 'magnitude'  perturb magnitude only, or 'phase'
%     dist         : 'normal'      'normal' (additive Gaussian std=sigma) or
%                                  'uniform' (multiplicative A->A(1+e),
%                                  e~Uniform[-sigma,sigma]; sigma = epsilon)
%     fast_peaks   : true         use findpeaks_fast in v24 + analysis
%     seed         : []           rng seed (omit for non-deterministic)
%     verbose      : false
%     show_plots   : true
%
%   Dependencies: perturb_method_v24, perturb_method_constrained_v2,
%                 findpeaks_fast, d1d2Convert.

    p = inputParser;
    addParameter(p, 'N',            9,                 @(v) mod(v,2)==1 && v>=3);
    addParameter(p, 'd_ideal',      0.04880,           @isnumeric);
    addParameter(p, 'phi_0',        0,                 @isnumeric);
    addParameter(p, 'null_phi',     [],                @isnumeric);
    addParameter(p, 'Max_iter',     60,                @isnumeric);
    addParameter(p, 'eps_dB',       -20,               @isnumeric);
    addParameter(p, 'threshold_dB', -20,               @isnumeric);
    addParameter(p, 'null_threshold_dB', -40,          @isnumeric);
    addParameter(p, 'method',       'v24',             @(s) ischar(s) || isstring(s));
    addParameter(p, 'cone_rad',     [],                @isnumeric);
    addParameter(p, 'max_outer_passes', 50,            @isnumeric);
    addParameter(p, 'sigma_list',   logspace(-3,1,41), @isnumeric);
    addParameter(p, 'n_trials',     300,               @isnumeric);
    addParameter(p, 'perturb_component', 'magnitude',  @(s) ischar(s) || isstring(s));
    addParameter(p, 'dist',         'normal',          @(s) ischar(s) || isstring(s));
    addParameter(p, 'fast_peaks',   true,              @islogical);
    addParameter(p, 'seed',         [],                @isnumeric);
    addParameter(p, 'verbose',      false,             @islogical);
    addParameter(p, 'show_plots',   true,              @islogical);
    parse(p, varargin{:}); a = p.Results;

    if ~isempty(a.seed), rng(a.seed); end

    freq = 3e9; lambda = 3e8/freq; k0 = 2*pi/lambda;
    [x0, y0] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    x = x0(:); y = y0(:);
    phi_0 = mod(a.phi_0, 2*pi);
    use_null = ~(isempty(a.null_phi) || any(isnan(a.null_phi)));
    null_phi = mod(a.null_phi, 2*pi);

    % ---- 1. Optimize on ideal layout ----
    method_key = lower(string(a.method));
    if use_null && any(method_key == ["constrained"])
        error('processing_error_analysis: method "%s" does not support null_phi.', a.method);
    end
    switch method_key
        case "v24"
            opt_args = {a.Max_iter, a.eps_dB, x, y, phi_0, ...
                'fast_peaks',      a.fast_peaks, ...
                'verbose',         false, ...
                'show_plots',      false, ...
                'show_final_plot', false, ...
                'return_funcs',    false, ...
                'full_loop',       false};
            if use_null
                opt_args = [opt_args, {'null_phi', null_phi}]; %#ok<AGROW>
            end
            opt = perturb_method_v24(opt_args{:});
            method_label = 'perturbation method';
        case "constrained"
            cone = a.cone_rad;
            if isempty(cone), cone = deg2rad(30); end
            opt = perturb_method_constrained_v2(a.Max_iter, a.eps_dB, x, y, phi_0, ...
                'cone_rad',         cone, ...
                'max_outer_passes', a.max_outer_passes, ...
                'fast_peaks',       a.fast_peaks, ...
                'verbose',          false, ...
                'show_plots',       false, ...
                'show_final_plot',  false, ...
                'return_funcs',     false);
            method_label = 'constrained';
        otherwise
            error('processing_error_analysis: unknown method "%s".', a.method);
    end
    A_eff = opt.A_eff(:);
    N = numel(A_eff);
    mag_eff   = abs(A_eff);
    phase_eff = angle(A_eff);

    perturb_component = lower(string(a.perturb_component));
    dist_key = lower(string(a.dist));
    if ~any(dist_key == ["normal", "uniform"])
        error('processing_error_analysis: unknown dist "%s" (use "normal" or "uniform").', a.dist);
    end
    switch perturb_component
        case "magnitude"
            sigma_desc = 'magnitude';
            if dist_key == "uniform"
                sigma_label = 'Amplitude perturbation half-width \epsilon  (A\rightarrowA(1+e))';
            else
                sigma_label = 'Magnitude perturbation std \sigma_A';
            end
        case "phase"
            sigma_desc = 'phase';
            if dist_key == "uniform"
                sigma_label = 'Phase perturbation half-width \epsilon  (\theta\rightarrow\theta(1+e))';
            else
                sigma_label = 'Phase perturbation std \sigma_\theta [rad]';
            end
        otherwise
            error('processing_error_analysis: unknown perturb_component "%s".', a.perturb_component);
    end
    if dist_key == "uniform"
        level_name = '\epsilon';
        lvl_txt    = 'epsilon';
        dist_label = 'uniform';
    else
        level_name = '\sigma';
        lvl_txt    = 'sigma';
        dist_label = 'normal';
    end

    % Pattern mesh and precomputed kernel
    M = 1000;
    phi = linspace(0, 2*pi, M+1); phi(end) = [];
    K   = exp(1j*k0*(x*cos(phi) + y*sin(phi)));   % NxM

    % Noiseless reference worst sidelobe
    F_ref     = (A_eff.') * K;
    ref_ws_dB = worst_sl_one(F_ref, phi, phi_0, a.fast_peaks);
    ref_null_dB = NaN;
    if use_null
        ref_null_dB = null_level_one(F_ref, phi, null_phi);
    end

    % ---- 2. MC sweep ----
    sigma_list = a.sigma_list(:);
    n_trials   = a.n_trials;
    nS         = numel(sigma_list);

    mean_ws   = nan(nS,1);
    std_ws    = nan(nS,1);
    median_ws = nan(nS,1);
    p25_ws    = nan(nS,1);
    p75_ws    = nan(nS,1);
    pct_break = nan(nS,1);
    mean_null = nan(nS,1);
    std_null  = nan(nS,1);
    pct_null_break = nan(nS,1);

    for s = 1:nS
        sigma   = sigma_list(s);
        switch dist_key
            case "normal"
                switch perturb_component
                    case "magnitude"
                        mag_noisy   = max(mag_eff + sigma * randn(N, n_trials), 0);
                        phase_noisy = phase_eff;
                    case "phase"
                        mag_noisy   = mag_eff;
                        phase_noisy = phase_eff + sigma * randn(N, n_trials);
                end
            case "uniform"
                % e ~ Uniform[-sigma, sigma], drawn independently per element & trial
                e = sigma * (2*rand(N, n_trials) - 1);
                switch perturb_component
                    case "magnitude"
                        mag_noisy   = max(mag_eff .* (1 + e), 0);   % A -> A(1+e)
                        phase_noisy = phase_eff;
                    case "phase"
                        mag_noisy   = mag_eff;
                        phase_noisy = phase_eff .* (1 + e);          % theta -> theta(1+e)
                end
        end

        A_noisy = mag_noisy .* exp(1j * phase_noisy);                     % NxT
        F_all   = A_noisy.' * K;                                          % TxM
        ws_t    = worst_sl_batch(F_all, phi, phi_0, a.fast_peaks);        % Tx1

        mean_ws(s)   = mean(ws_t);
        std_ws(s)    = std(ws_t);
        median_ws(s) = median(ws_t);
        p25_ws(s)    = prctile(ws_t, 25);
        p75_ws(s)    = prctile(ws_t, 75);
        pct_break(s) = mean(ws_t > a.threshold_dB);
        if use_null
            null_t = null_level_batch(F_all, phi, null_phi);
            mean_null(s) = mean(null_t);
            std_null(s)  = std(null_t);
            pct_null_break(s) = mean(null_t > a.null_threshold_dB);
        end

        if a.verbose
            if use_null
                fprintf(['sigma=%.4g:  meanSL=%.2f  stdSL=%.2f  P(SL break)=%.2f  ' ...
                         'meanNull=%.2f  P(null break)=%.2f\n'], ...
                    sigma, mean_ws(s), std_ws(s), pct_break(s), ...
                    mean_null(s), pct_null_break(s));
            else
                fprintf('sigma=%.4g:  mean=%.2f  std=%.2f  median=%.2f  P(break)=%.2f\n', ...
                    sigma, mean_ws(s), std_ws(s), median_ws(s), pct_break(s));
            end
        end
    end

    % ---- 3. Find breaking sigma (mean worst SL crosses threshold) ----
    sigma_break = find_threshold_sigma(sigma_list, mean_ws, a.threshold_dB);
    sigma_50pct = find_threshold_sigma(sigma_list, pct_break, 0.5);
    sigma_null_break = NaN;
    sigma_null_50pct = NaN;
    if use_null
        sigma_null_break = find_threshold_sigma(sigma_list, mean_null, a.null_threshold_dB);
        sigma_null_50pct = find_threshold_sigma(sigma_list, pct_null_break, 0.5);
    end

    res.A_eff        = A_eff;
    res.sigma_list   = sigma_list;
    res.mean_ws      = mean_ws;
    res.std_ws       = std_ws;
    res.median_ws    = median_ws;
    res.p25_ws       = p25_ws;
    res.p75_ws       = p75_ws;
    res.pct_break    = pct_break;
    res.mean_null    = mean_null;
    res.std_null     = std_null;
    res.pct_null_break = pct_null_break;
    res.sigma_break  = sigma_break;
    res.sigma_50pct  = sigma_50pct;
    res.sigma_null_break = sigma_null_break;
    res.sigma_null_50pct = sigma_null_50pct;
    res.threshold_dB = a.threshold_dB;
    res.ref_ws_dB    = ref_ws_dB;
    res.null_threshold_dB = a.null_threshold_dB;
    res.ref_null_dB  = ref_null_dB;
    res.n_trials     = n_trials;
    res.N            = N;
    res.lambda       = lambda;
    res.method       = char(method_key);
    res.method_label = method_label;
    res.perturb_component = char(perturb_component);
    res.dist         = char(dist_key);
    res.dist_label   = dist_label;
    res.level_name   = level_name;
    res.sigma_label  = sigma_label;
    res.sigma_desc   = sigma_desc;
    res.focus_angle  = phi_0;
    res.focus_angle_deg = rad2deg(phi_0);
    res.null_angle   = [];
    res.null_angle_deg = [];
    if use_null
        res.null_angle = null_phi;
        res.null_angle_deg = rad2deg(null_phi);
    end
    res.params       = a;

    fprintf('[%s | %s | %s] noiseless worst sidelobe = %.2f dB\n', ...
            method_label, dist_label, sigma_desc, ref_ws_dB);
    fprintf('[%s | %s | %s] mean worst SL crosses %.0f dB at %s >= %.4g (interp).\n', ...
            method_label, dist_label, sigma_desc, a.threshold_dB, lvl_txt, sigma_break);
    fprintf('[%s | %s | %s] P(break) crosses 50%%      at %s >= %.4g (interp).\n', ...
            method_label, dist_label, sigma_desc, lvl_txt, sigma_50pct);
    if use_null
        fprintf('[%s | %s | %s] noiseless null level = %.2f dB\n', ...
                method_label, dist_label, sigma_desc, ref_null_dB);
        fprintf('[%s | %s | %s] mean null crosses %.0f dB at %s >= %.4g (interp).\n', ...
                method_label, dist_label, sigma_desc, a.null_threshold_dB, lvl_txt, sigma_null_break);
        fprintf('[%s | %s | %s] P(null break) crosses 50%% at %s >= %.4g (interp).\n', ...
                method_label, dist_label, sigma_desc, lvl_txt, sigma_null_50pct);
    end

    if ~a.show_plots, return; end

    % ---- Plot 1: mean ± std worst sidelobe vs sigma ----
    figure('Name', sprintf('Processing error (%s, %s, %s): worst sidelobe vs %s', ...
        method_label, dist_label, sigma_desc, lvl_txt));
    fill([sigma_list; flipud(sigma_list)], ...
         [mean_ws - std_ws; flipud(mean_ws + std_ws)], ...
         [0.6 0.8 1.0], 'FaceAlpha', 0.35, 'EdgeColor','none'); hold on;
    semilogx(sigma_list, mean_ws,   '-o', 'LineWidth', 1.5);
    semilogx(sigma_list, median_ws, '--', 'LineWidth', 1.0);
    yline(a.threshold_dB, 'k--', sprintf('%.0f dB', a.threshold_dB));
    yline(ref_ws_dB,      'g:',  sprintf('noiseless = %.2f dB', ref_ws_dB));
    if ~isnan(sigma_break)
        xline(sigma_break, 'r:', sprintf('break %s = %.3g', level_name, sigma_break));
    end
    set(gca,'XScale','log');
    xlabel(sigma_label);
    ylabel('Worst sidelobe [dB] (rel own peak)');
    grid on;
    title(sprintf('Processing error MC (%s, %s, %s): %d trials/level, N=%d', ...
        method_label, dist_label, sigma_desc, n_trials, N));
    legend({'\pm 1 std', 'mean', 'median', sprintf('%.0f dB', a.threshold_dB), ...
            sprintf('noiseless ref'), sprintf('break %s', level_name)}, ...
           'Location','northoutside', 'Orientation','horizontal');

    % ---- Plot 2: probability of breaking vs sigma ----
    figure('Name', sprintf('Processing error (%s, %s, %s): P(break) vs %s', ...
        method_label, dist_label, sigma_desc, lvl_txt));
    semilogx(sigma_list, pct_break, '-s', 'LineWidth', 1.5); hold on;
    yline(0.5,  'k--', '50%');
    if ~isnan(sigma_50pct)
        xline(sigma_50pct, 'r:', sprintf('%s at 50%% = %.3g', level_name, sigma_50pct));
    end
    xlabel(sigma_label);
    ylabel(sprintf('P(worst SL > %.0f dB)', a.threshold_dB));
    ylim([0 1]); grid on;
    title(sprintf('Probability of breaking the threshold (%s, %s, %s, n=%d)', ...
        method_label, dist_label, sigma_desc, n_trials));
    legend({sprintf('P(worst SL > %.0f dB)', a.threshold_dB), '50%', sprintf('%s at 50%%', level_name)}, ...
           'Location','northoutside', 'Orientation','horizontal');
end


function nl = null_level_one(F, phi, null_phi)
    Fmag = abs(F);
    Fn = interp1(phi, F, null_phi, 'linear', 'extrap');
    nl = 10*log10(abs(Fn).^2 / max(Fmag).^2);
end


function nl = null_level_batch(F_all, phi, null_phi)
    Fmag_all = abs(F_all);
    Fmax = max(Fmag_all, [], 2);
    Fn = interp1(phi, F_all.', null_phi, 'linear', 'extrap').';
    nl = 10*log10(abs(Fn).^2 ./ Fmax.^2);
end


function ws = worst_sl_one(F, phi, phi_0, fast_peaks)
    Fmag = abs(F);
    if fast_peaks
        [pv,pl] = findpeaks_fast(Fmag, phi);
    else
        [pv,pl] = findpeaks_circular(Fmag, phi);
    end
    if isempty(pv), ws = -Inf; return; end
    [~, im] = min(abs(atan2(sin(pl - phi_0), cos(pl - phi_0))));
    pv(im) = [];
    if isempty(pv), ws = -Inf; return; end
    ws = 10*log10(max(pv).^2 / max(Fmag).^2);
end


function ws = worst_sl_batch(F_all, phi, phi_0, fast_peaks)
% F_all is TxM. Returns Tx1 worst sidelobe in dB rel own peak.
    [T, ~] = size(F_all);
    Fmag_all = abs(F_all);
    if fast_peaks
        % Vectorized strict-greater-than circular peak mask (T x M)
        isPk = Fmag_all > Fmag_all(:, [end 1:end-1]) & ...
               Fmag_all > Fmag_all(:, [2:end 1]);
    end
    Fmax = max(Fmag_all, [], 2);
    ws = -Inf(T,1);
    for t = 1:T
        if fast_peaks
            pk_idx = find(isPk(t,:));
            pv = Fmag_all(t, pk_idx);
            pl = phi(pk_idx);
        else
            [pv, pl] = findpeaks_circular(Fmag_all(t,:), phi);
        end
        if isempty(pv), continue; end
        [~, im] = min(abs(atan2(sin(pl - phi_0), cos(pl - phi_0))));
        pv(im) = [];
        if isempty(pv), continue; end
        ws(t) = 10*log10(max(pv).^2 / Fmax(t)^2);
    end
end


function s_thr = find_threshold_sigma(sigma_list, metric, threshold)
% Linear interpolation in (log sigma, metric) for the smallest sigma at
% which metric exceeds threshold. NaN if no crossing exists.
    idx = find(metric > threshold, 1, 'first');
    if isempty(idx)
        s_thr = NaN; return;
    end
    if idx == 1
        s_thr = sigma_list(1); return;
    end
    s1 = log10(sigma_list(idx-1)); s2 = log10(sigma_list(idx));
    m1 = metric(idx-1);            m2 = metric(idx);
    if m2 == m1
        s_thr = sigma_list(idx); return;
    end
    s_thr = 10^(s1 + (threshold - m1)*(s2 - s1)/(m2 - m1));
end
