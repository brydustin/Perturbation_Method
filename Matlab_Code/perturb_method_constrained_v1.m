%% Constrained Perturbative Method (v1)
% Implements the algorithm in Constrained_Perturbative_Method.tex, wrapped in
% an outer Gamma-refresh loop.
%
% Each INNER pass is the proven algorithm: with a fixed sample set Gamma of
% size M = L-1, the iteration f_{n+1} = f_n - (f_n(beta)/||M_beta||^2) M_beta
% converges geometrically to the exact constrained interpolant f* (Theorem 2).
% The OUTER loop refreshes Gamma to the current worst L-1 dense-mesh peaks
% and reruns the inner algorithm, warm-started from the current f.  Each
% inner pass remains exactly the proven algorithm; the outer loop is a
% heuristic for converting "controlled-sample max sidelobe" into "dense-mesh
% max sidelobe."  An intrinsic Chebyshev floor exists for any finite L; if
% eps_dB is below it the function exits when the iteration budget runs out
% (overall_converged = false in the results).
%
% Math symbols:
%   kappa_j(phi) = exp(+i*k0*(x_j*cos(phi) + y_j*sin(phi)))
%   K_alpha(phi) = sum_j conj(kappa_j(alpha)) * kappa_j(phi)
%   M_alpha      = K_alpha - (K_alpha(phi_0)/L) * K_phi0
%   ||M_alpha||^2 = L - |K_alpha(phi_0)|^2 / L
%
% Required: Max_iter, eps_dB, x, y, phi_0
% Optional name-value:
%   gamma_pts        : initial Gamma. Default: top L-1 sidelobes of |K_phi0|.
%   max_outer_passes : default 10. Set to 1 for the strict single-pass version.
%   cone_rad         : exclusion half-width around phi_0 when refreshing Gamma.
%   z, theta_0       : for 3D gain reporting.
%   show_plots, show_final_plot, verbose, return_funcs
%
% Dependencies on path: findpeaks_circular, directivity_met_v2, plot_pattern_v5.
%
function results = perturb_method_constrained_v1(varargin)

    %% ---- Parse inputs ----
    p = inputParser;
    p.FunctionName = 'perturb_method_constrained_v1';
    addRequired (p, 'Max_iter', @isnumeric);
    addRequired (p, 'eps_dB',   @isnumeric);
    addRequired (p, 'x',        @isnumeric);
    addRequired (p, 'y',        @isnumeric);
    addRequired (p, 'phi_0',    @isnumeric);
    addOptional (p, 'z',                  [], @isnumeric);
    addOptional (p, 'gamma_pts',          [], @isnumeric);
    addParameter(p, 'cone_rad',           [], @isnumeric);
    addParameter(p, 'max_outer_passes',   10, @isnumeric);
    addOptional (p, 'theta_0',      pi*0.5,   @isnumeric);
    addOptional (p, 'show_plots',      false, @islogical);
    addOptional (p, 'show_final_plot', false, @islogical);
    addOptional (p, 'verbose',         false, @islogical);
    addOptional (p, 'return_funcs',    false, @islogical);
    parse(p, varargin{:});
    a = p.Results;

    Max_iter         = a.Max_iter;
    eps_dB           = a.eps_dB;
    x                = a.x(:);
    y                = a.y(:);
    z                = a.z(:);
    phi_0            = mod(a.phi_0, 2*pi);
    theta_0          = mod(a.theta_0, 2*pi);
    user_gamma_pts   = a.gamma_pts(:);
    cone_rad         = a.cone_rad;
    max_outer_passes = a.max_outer_passes;
    show_plots       = a.show_plots;
    show_final_plot  = a.show_final_plot;
    verbose          = a.verbose;
    return_funcs     = a.return_funcs;

    L = numel(x);
    if L < 2, error('x,y must contain at least two elements.'); end

    %% ---- RF / mesh ----
    freq   = 3e9;
    lambda = 3e8 / freq;     %#ok<NASGU>
    k0     = 2*pi*freq / 3e8;

    mesh_len   = 1000;
    phi        = linspace(0, 2*pi, mesh_len+1); phi(end) = [];
    theta_mesh = linspace(0, pi,   mesh_len);

    %% ---- Pattern-space helpers ----
    function kvec = kappa_vec(alpha)
        kvec = exp(1j * k0 * (x*cos(alpha) + y*sin(alpha)));
    end
    function fvals = eval_f(c, ang)
        ang  = ang(:).';
        Kmat = exp(1j * k0 * (x*cos(ang) + y*sin(ang)));
        fvals = (c.') * Kmat;
    end

    kappa_phi0  = kappa_vec(phi_0);
    coef_K_phi0 = conj(kappa_phi0);
    nKphi       = coef_K_phi0 / sqrt(L);
    P_V         = eye(L) - nKphi * (nKphi');     % projector onto V

    %% ---- Refresh Gamma from the dense-mesh peaks of a given pattern ----
    function gpts = refresh_gamma(coef_now)
        Fnow = eval_f(coef_now, phi);
        [pv, pl] = findpeaks_circular(abs(Fnow), phi);
        if isempty(pv)
            gpts = mod(phi_0 + linspace(2*pi/L, 2*pi - 2*pi/L, L-1).', 2*pi);
            return;
        end
        d_main = abs(atan2(sin(pl - phi_0), cos(pl - phi_0)));
        [~, im] = min(d_main);
        pv(im) = []; pl(im) = [];
        if ~isempty(cone_rad) && ~isempty(pl)
            d = mod(pl - phi_0 + pi, 2*pi) - pi;
            keep = abs(d) > cone_rad;
            pv = pv(keep); pl = pl(keep);
        end
        if isempty(pv)
            gpts = mod(phi_0 + linspace(2*pi/L, 2*pi - 2*pi/L, L-1).', 2*pi);
            return;
        end
        [~, ix] = sort(pv, 'descend');
        ntake = min(L-1, numel(ix));
        gpts = mod(pl(ix(1:ntake)), 2*pi);
    end

    %% ---- Compute everything that depends on a given Gamma ----
    function pd = compute_pass_data(gpts)
        gpts = mod(gpts(:), 2*pi);
        Mloc = numel(gpts);

        Kappa_gam = zeros(L, Mloc);
        for j = 1:Mloc, Kappa_gam(:, j) = kappa_vec(gpts(j)); end

        Kalpha_at_phi0 = (Kappa_gam') * kappa_phi0;          % M x 1
        Kphi0_at_gamma = (coef_K_phi0.') * Kappa_gam;        % 1 x M

        coef_M_gam = conj(Kappa_gam) - conj(kappa_phi0) * (Kalpha_at_phi0.' / L);
        M_norm_sq  = L - (abs(Kalpha_at_phi0).^2) / L;

        G_mat = coef_M_gam' * coef_M_gam;
        b     = -(Kphi0_at_gamma.');
        if Mloc == L-1
            a_star = G_mat \ b;
        else
            a_star = pinv(G_mat) * b;
        end
        coef_hstar  = coef_M_gam * a_star;
        h_star_norm = sqrt(real(coef_hstar' * coef_hstar));

        E_onV = (Kappa_gam.') * P_V;
        sv    = svd(E_onV);
        if isempty(sv)
            sigma_min_E = 0;
        else
            sv_keep = sv(sv > 1e-10 * max(sv));
            if isempty(sv_keep), sigma_min_E = 0;
            else,                sigma_min_E = min(sv_keep);
            end
        end
        c_Gamma_lower = sigma_min_E / sqrt(max(Mloc, 1));
        q_rate_upper  = sqrt(max(0, 1 - c_Gamma_lower^2 / L));

        pd = struct( ...
            'gamma_pts',     gpts, ...
            'M',             Mloc, ...
            'Kappa_gam',     Kappa_gam, ...
            'coef_M_gam',    coef_M_gam, ...
            'M_norm_sq',     M_norm_sq, ...
            'coef_hstar',    coef_hstar, ...
            'h_star_norm',   h_star_norm, ...
            'c_Gamma_lower', c_Gamma_lower, ...
            'q_rate_upper',  q_rate_upper);
    end

    %% ---- Initial Gamma ----
    if isempty(user_gamma_pts)
        gamma_pts = refresh_gamma(coef_K_phi0);
    else
        gamma_pts = user_gamma_pts;
    end

    %% ---- Pre-allocate stores ----
    max_sidelobe_store        = nan(Max_iter+1, 1);   % at controlled Gamma
    dense_max_sidelobe_store  = nan(Max_iter+1, 1);   % over dense mesh
    dense_max_phi_store       = nan(Max_iter+1, 1);
    decrement_store           = nan(Max_iter+1, 1);
    distance_to_fstar_store   = nan(Max_iter+1, 1);   % w.r.t. current pass's h*
    focus_value_store         = nan(Max_iter+1, 1);
    focus_value_store_dB      = nan(Max_iter+1, 1);
    directivity_metric_1_beamwidth_store = nan(Max_iter+1, 1);
    pass_idx_store            = zeros(Max_iter+1, 1);

    if return_funcs
        F_store   = nan(Max_iter+1, mesh_len);
        G2D_store = nan(Max_iter+1, 1);
        G3D_store = nan(Max_iter+1, 1);
    end

    A_store     = {coef_K_phi0};
    A_eff_store = {coef_K_phi0};
    phi_store   = phi_0;

    pass_start_iter    = [];
    pass_gamma_pts     = {};
    pass_coef_hstar    = {};
    pass_h_star_norm   = [];
    pass_q_rate_upper  = [];
    pass_c_Gamma_lower = [];

    %% ---- Recorder ----
    function record_iter(idx, coef_now, pd, pass_id)
        F_local = eval_f(coef_now, phi);
        Fmag    = abs(F_local);
        F_at_0  = eval_f(coef_now, phi_0);

        focus_value_store(idx)    = F_at_0;
        focus_value_store_dB(idx) = 10*log10(abs(F_at_0).^2 / max(Fmag).^2);

        f_g = (coef_now.') * pd.Kappa_gam;
        if pd.M > 0
            [mv, mi] = max(abs(f_g));
            max_sidelobe_store(idx) = 10*log10(mv.^2 / max(Fmag).^2);
        else
            mi = 1;
        end %#ok<NASGU>

        [pkdB, pkphi] = dense_peak_dB(F_local);
        dense_max_sidelobe_store(idx) = pkdB;
        dense_max_phi_store(idx)      = pkphi;

        h_now = coef_now - coef_K_phi0;
        distance_to_fstar_store(idx) = sqrt(real( ...
            (h_now - pd.coef_hstar)' * (h_now - pd.coef_hstar)));

        bw = directivity_met_v2(phi, F_local, phi_0);
        directivity_metric_1_beamwidth_store(idx) = bw.beamwidth;

        pass_idx_store(idx) = pass_id;

        if return_funcs
            F_store(idx, :) = F_local(:).';
            G2D_store(idx)  = gain_calc(F_local, phi, phi_0);
            G3D_store(idx)  = gain_calc_3D( ...
                F3D(phi, theta_mesh, coef_now, x, y, z, [], k0), ...
                phi, theta_mesh, phi_0, theta_0);
        end
    end

    function [pkdB, pkphi] = dense_peak_dB(F_local)
        Fmag = abs(F_local);
        [pv, pl] = findpeaks_circular(Fmag, phi);
        if isempty(pv), pkdB = NaN; pkphi = NaN; return; end
        d_main = abs(atan2(sin(pl - phi_0), cos(pl - phi_0)));
        [~, im] = min(d_main);
        pv(im) = []; pl(im) = [];
        if ~isempty(cone_rad) && ~isempty(pl)
            d = mod(pl - phi_0 + pi, 2*pi) - pi;
            keep = abs(d) > cone_rad;
            pv = pv(keep); pl = pl(keep);
        end
        if isempty(pv), pkdB = -Inf; pkphi = NaN; return; end
        [pkmag, ix] = max(pv);
        pkdB  = 10*log10(pkmag.^2 / max(Fmag).^2);
        pkphi = pl(ix);
    end

    %% ---- Initial state ----
    tic;
    iter   = 0;
    coef_f = coef_K_phi0;            % h_0 = 0
    pd     = compute_pass_data(gamma_pts);
    record_iter(1, coef_f, pd, 0);   % pass 0 = initial state

    %% ---- Outer / inner loops ----
    overall_converged = false;
    pass = 0;
    while pass < max_outer_passes
        pass = pass + 1;

        if pass > 1
            gamma_pts = refresh_gamma(coef_f);
            pd        = compute_pass_data(gamma_pts);
        end

        pass_start_iter   (end+1) = iter + 1;        %#ok<AGROW>
        pass_gamma_pts    {end+1} = pd.gamma_pts;    %#ok<AGROW>
        pass_coef_hstar   {end+1} = pd.coef_hstar;   %#ok<AGROW>
        pass_h_star_norm  (end+1) = pd.h_star_norm;  %#ok<AGROW>
        pass_q_rate_upper (end+1) = pd.q_rate_upper; %#ok<AGROW>
        pass_c_Gamma_lower(end+1) = pd.c_Gamma_lower;%#ok<AGROW>

        if verbose
            fprintf(['Pass %d: M=%d, ||h*||=%.4g, c_Gamma>=%.4g, q<=%.4g, ' ...
                     'starting at iter %d\n'], pass, pd.M, pd.h_star_norm, ...
                     pd.c_Gamma_lower, pd.q_rate_upper, iter+1);
        end

        % Inner loop: proven projection updates with fixed Gamma
        while iter < Max_iter
            f_g = (coef_f.') * pd.Kappa_gam;
            [worst, jmax] = max(abs(f_g));

            F_now = eval_f(coef_f, phi);
            cur_max_sample_dB = 10*log10(worst.^2 / max(abs(F_now)).^2);
            if cur_max_sample_dB <= eps_dB
                if verbose
                    fprintf(['  Pass %d inner-converged at iter %d ' ...
                             '(sample-max %.2f dB <= %.2f dB).\n'], ...
                             pass, iter, cur_max_sample_dB, eps_dB);
                end
                break;
            end

            scalar     = f_g(jmax) / pd.M_norm_sq(jmax);
            delta_coef = -scalar * pd.coef_M_gam(:, jmax);
            coef_f     = coef_f + delta_coef;

            iter = iter + 1;
            decrement_store(iter+1) = abs(f_g(jmax)).^2 / pd.M_norm_sq(jmax);

            A_store    {end+1} = delta_coef;       %#ok<AGROW>
            A_eff_store{end+1} = coef_f;           %#ok<AGROW>
            phi_store  (end+1) = pd.gamma_pts(jmax); %#ok<AGROW>

            record_iter(iter+1, coef_f, pd, pass);

            if verbose
                fprintf(['  P%d I%d: theta=%.4f, |f|=%.4g, decr=%.4g, ' ...
                         '||h-h*||=%.4g, dense-max=%.2f dB\n'], ...
                         pass, iter, pd.gamma_pts(jmax), abs(f_g(jmax)), ...
                         decrement_store(iter+1), ...
                         distance_to_fstar_store(iter+1), ...
                         dense_max_sidelobe_store(iter+1));
            end

            if show_plots
                F_plot = eval_f(coef_f, phi);
                plot_pattern_v5(phi, F_plot, ...
                    'label',  sprintf('Pass %d, iter %d', pass, iter), ...
                    'phi_0',  phi_0, ...
                    'phi_s',  pd.gamma_pts, ...
                    'show_plots', true, ...
                    'iter',   iter);
            end
        end

        % Outer stop test: dense-mesh peaks
        F_now           = eval_f(coef_f, phi);
        [pkdB, ~]       = dense_peak_dB(F_now);
        if isnan(pkdB) || pkdB <= eps_dB
            overall_converged = true;
            if verbose
                fprintf(['Pass %d: dense-mesh max sidelobe %.2f dB <= %.2f dB. ' ...
                         'OVERALL DONE.\n'], pass, pkdB, eps_dB);
            end
            break;
        end
        if iter >= Max_iter
            if verbose
                fprintf(['Iteration budget (%d) exhausted in pass %d. ' ...
                         'Dense-mesh max sidelobe = %.2f dB > %.2f dB.\n'], ...
                         Max_iter, pass, pkdB, eps_dB);
            end
            break;
        end
        if verbose
            fprintf(['Pass %d: dense-mesh max sidelobe %.2f dB > %.2f dB. ' ...
                     'Refreshing Gamma.\n'], pass, pkdB, eps_dB);
        end
    end

    if ~overall_converged && iter < Max_iter && pass >= max_outer_passes
        warning(['Reached max_outer_passes (%d) without dense-mesh ' ...
                 'convergence. The intrinsic Chebyshev floor for L=%d may ' ...
                 'be above eps_dB=%.2f dB.'], max_outer_passes, L, eps_dB);
    end

    %% ---- Final pattern + reporting ----
    F_total    = eval_f(coef_f, phi);
    F_star     = eval_f(coef_K_phi0 + pd.coef_hstar, phi);
    Fmag       = abs(F_total);
    F_at_phi_0 = eval_f(coef_f, phi_0);

    [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
    if ~isempty(peakVals)
        d_main = abs(atan2(sin(peakLocs - phi_0), cos(peakLocs - phi_0)));
        [~, mainIdx] = min(d_main);
        Big_phi_final = peakLocs(mainIdx);
        Big_Val_final = peakVals(mainIdx);
        peakVals(mainIdx) = []; peakLocs(mainIdx) = [];
        if isempty(peakVals)
            Slobe_fin = []; phi_s_fin = [];
        else
            peakVals_db = 10*log10((peakVals.^2) / max(Fmag).^2);
            [Slobe_fin, sortIx] = sort(peakVals_db, 'descend');
            phi_s_fin = peakLocs(sortIx);
        end
    else
        Big_phi_final = phi_0;
        Big_Val_final = abs(F_at_phi_0);
        Slobe_fin = []; phi_s_fin = [];
    end

    if (show_plots || show_final_plot)
        plot_pattern_v5(phi, F_total, ...
            'label',         'Final Plot: Constrained Perturbative Method', ...
            'phi_0',         phi_0, ...
            'phi_s',         phi_s_fin, ...
            'Slobe',         Slobe_fin, ...
            'iter',          iter, ...
            'show_plots',    true, ...
            'cone_rad',      cone_rad, ...
            'Big_phi',       Big_phi_final);
    end

    %% ---- Pack results ----
    results.method                = 'constrained_v1';
    results.final_iteration       = iter;
    results.final_epoch           = iter;
    results.total_time            = toc;
    results.focus_angle           = phi_0;
    results.focus_angle_deg       = round(rad2deg(phi_0));
    results.cone_rad              = cone_rad;
    results.null_angle            = [];
    results.null_angle_deg        = [];

    % Outer-loop / pass diagnostics
    results.overall_converged     = overall_converged;
    results.num_passes            = pass;
    results.max_outer_passes      = max_outer_passes;
    results.pass_start_iter       = pass_start_iter;
    results.pass_gamma_pts        = pass_gamma_pts;
    results.pass_coef_hstar       = pass_coef_hstar;
    results.pass_h_star_norm      = pass_h_star_norm;
    results.pass_q_rate_upper     = pass_q_rate_upper;
    results.pass_c_Gamma_lower    = pass_c_Gamma_lower;
    results.pass_idx_store        = pass_idx_store;

    % Final-pass quantities (h* etc. for the LAST pass that ran)
    results.gamma_pts             = pd.gamma_pts;
    results.M                     = pd.M;
    results.L                     = L;
    results.coef_K_phi0           = coef_K_phi0;
    results.coef_hstar            = pd.coef_hstar;
    results.coef_f                = coef_f;
    results.h_star_norm           = pd.h_star_norm;
    results.q_rate_upper          = pd.q_rate_upper;
    results.c_Gamma_lower         = pd.c_Gamma_lower;
    results.M_norm_sq             = pd.M_norm_sq;

    % Per-iteration stores
    results.decrement_store          = decrement_store;
    results.distance_to_fstar_store  = distance_to_fstar_store;
    results.max_sidelobe_store       = max_sidelobe_store;
    results.dense_max_sidelobe_store = dense_max_sidelobe_store;
    results.dense_max_phi_store      = dense_max_phi_store;
    results.directivity_metric_1_beamwidth_store = directivity_metric_1_beamwidth_store;
    results.focus_value_store        = abs(focus_value_store);
    results.focus_value_store_dB     = focus_value_store_dB;
    results.fstar_function           = F_star;
    results.final_function           = F_total;
    results.F_at_phi_0               = abs(F_at_phi_0);

    % v23-style compatibility outputs
    results.A_store         = A_store;
    results.A_eff_store     = A_eff_store;
    results.phi_store       = phi_store;
    results.A_eff           = coef_f;
    results.delta_eff       = zeros(L, 1);
    results.x_pos           = x;
    results.y_pos           = y;
    results.phi_s_fin       = phi_s_fin;
    results.Big_phi_final   = Big_phi_final;
    results.Big_Val_final   = Big_Val_final;
    results.initial_m       = pd.M;
    results.m               = pd.M;

    if return_funcs
        results.F_store   = F_store;
        results.G2D_store = G2D_store;
        results.G3D_store = G3D_store;
    end

    %% ---- 3D gain helpers (only used when return_funcs=true) ----
    function F = F3D(phi_loc, theta_loc, A_loc, x_loc, y_loc, z_loc, delta_loc, k0_loc)
        A_loc = A_loc(:); x_loc = x_loc(:); y_loc = y_loc(:);
        if isempty(z_loc),     z_loc     = zeros(size(A_loc)); else, z_loc     = z_loc(:);     end
        if isempty(delta_loc), delta_loc = zeros(size(A_loc)); else, delta_loc = delta_loc(:); end
        phi_loc   = phi_loc(:).';
        theta_loc = theta_loc(:).';
        [PHI, THETA] = meshgrid(phi_loc, theta_loc);
        xr = reshape(x_loc, [], 1, 1); yr = reshape(y_loc, [], 1, 1);
        zr = reshape(z_loc, [], 1, 1); dr = reshape(delta_loc, [], 1, 1);
        TH = reshape(THETA, 1, size(THETA,1), size(THETA,2));
        PH = reshape(PHI,   1, size(PHI,1),   size(PHI,2));
        phase = k0_loc * (xr.*sin(TH).*cos(PH) + yr.*sin(TH).*sin(PH) + zr.*cos(TH)) + dr;
        E = cos((pi/2) * cos(TH)) ./ sin(TH);
        E(~isfinite(E)) = 0;
        Ar = reshape(A_loc, [], 1, 1);
        F = squeeze(sum(Ar .* E .* exp(1j * phase), 1));
    end

    function G = gain_calc(F_total_loc, phi_mesh, phi_dir)
        phi_mesh = phi_mesh(:).';
        I = trapz(phi_mesh, abs(F_total_loc).^2, 2);
        F_at = interp1(phi_mesh, F_total_loc.', phi_dir, 'linear', 'extrap').';
        G = 10*log10((abs(F_at).^2 * 4*pi) ./ I);
    end

    function G3 = gain_calc_3D(F_total_loc, phi_mesh, theta_mesh_loc, phi_dir, theta_dir)
        phi_mesh       = phi_mesh(:).';
        theta_mesh_loc = theta_mesh_loc(:);
        P = abs(F_total_loc).^2; P(~isfinite(P)) = 0;
        I_phi = trapz(phi_mesh, P .* sin(theta_mesh_loc), 2);
        I = trapz(theta_mesh_loc, I_phi);
        F0 = interp2(phi_mesh, theta_mesh_loc, F_total_loc, phi_dir, theta_dir, 'linear', 0);
        G3 = 10*log10((abs(F0).^2 * 4*pi) / I);
    end

end
