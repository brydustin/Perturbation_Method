function results = perturb_method_constrained_v2(varargin)
%PERTURB_METHOD_CONSTRAINED_V2  Heavily optimized rewrite of v1.
%   Same algorithm and result fields. Hot-path optimizations:
%     - Precomputed K = exp(i*k0*(x*cos(phi)+y*sin(phi))); F = (c.')*K
%       Replaces eval_f's per-call exp(NxM) construction.
%     - directivity_met_v2 only called when return_funcs=true (per-iter cost gone)
%     - 'fast_peaks' (default true) selects findpeaks_fast over findpeaks_circular
%     - record_iter writes pre-allocated rows; F_store optional
%
%   Same name-value parameters as v1, plus:
%     'fast_peaks'      (default true)

    p = inputParser; p.FunctionName = 'perturb_method_constrained_v2';
    addRequired (p,'Max_iter',@isnumeric); addRequired(p,'eps_dB',@isnumeric);
    addRequired (p,'x',@isnumeric); addRequired(p,'y',@isnumeric); addRequired(p,'phi_0',@isnumeric);
    addOptional (p,'z',[],@isnumeric);
    addOptional (p,'gamma_pts',[],@isnumeric);
    addParameter(p,'cone_rad',[],@isnumeric);
    addParameter(p,'max_outer_passes',50,@isnumeric);
    addOptional (p,'theta_0',pi*0.5,@isnumeric);
    addOptional (p,'show_plots',false,@islogical);
    addOptional (p,'show_final_plot',false,@islogical);
    addOptional (p,'verbose',false,@islogical);
    addOptional (p,'return_funcs',false,@islogical);
    addParameter(p,'fast_peaks',true,@islogical);
    parse(p,varargin{:}); a = p.Results;

    Max_iter=a.Max_iter; eps_dB=a.eps_dB;
    x=a.x(:); y=a.y(:); z=a.z(:);
    phi_0   = mod(a.phi_0,2*pi);
    theta_0 = mod(a.theta_0,2*pi);
    cone_rad=a.cone_rad; max_outer_passes=a.max_outer_passes;
    show_plots=a.show_plots; show_final_plot=a.show_final_plot;
    verbose=a.verbose; return_funcs=a.return_funcs; fast_peaks=a.fast_peaks;

    L = numel(x);
    if L<2, error('x,y must contain at least two elements.'); end

    k0 = 2*pi*3e9/3e8;
    M = 1000;
    phi = linspace(0,2*pi,M+1); phi(end)=[];

    % Precomputed kernel: K(j,m) = exp(i*k0*(x_j cos phi_m + y_j sin phi_m))
    K = exp(1j*k0*(x*cos(phi) + y*sin(phi)));   % LxM

    kappa_phi0  = exp(1j*k0*(x*cos(phi_0)+y*sin(phi_0)));   % Lx1
    coef_K_phi0 = conj(kappa_phi0);
    nKphi       = coef_K_phi0 / sqrt(L);
    P_V         = eye(L) - nKphi*(nKphi');

    % Initial Gamma
    if isempty(a.gamma_pts)
        gamma_pts = refresh_gamma_local((coef_K_phi0.')*K, phi, phi_0, cone_rad, L, fast_peaks);
    else
        gamma_pts = a.gamma_pts(:);
    end

    % Pre-allocate stores
    nan1 = nan(Max_iter+1,1);
    max_sidelobe_store=nan1; dense_max_sidelobe_store=nan1; dense_max_phi_store=nan1;
    decrement_store=nan1; distance_to_fstar_store=nan1;
    focus_value_store=nan1; focus_value_store_dB=nan1;
    directivity_metric_1_beamwidth_store=nan1;
    pass_idx_store = zeros(Max_iter+1,1);

    if return_funcs
        F_store   = nan(Max_iter+1,M);
        G2D_store = nan(Max_iter+1,1);
        G3D_store = nan(Max_iter+1,1);
        theta_mesh = linspace(0,pi,M);
    end

    cap = Max_iter+2;
    A_store     = cell(1,cap); A_store{1}=coef_K_phi0;
    A_eff_store = cell(1,cap); A_eff_store{1}=coef_K_phi0;
    phi_store   = nan(1,cap);  phi_store(1)=phi_0;
    ns = 1;

    pass_start_iter    = [];
    pass_gamma_pts     = {};
    pass_coef_hstar    = {};
    pass_h_star_norm   = [];
    pass_q_rate_upper  = [];
    pass_c_Gamma_lower = [];

    tic;
    iter = 0;
    coef_f = coef_K_phi0;
    pd = compute_pass_data_local(gamma_pts,x,y,k0,kappa_phi0,coef_K_phi0,P_V,L);
    record_iter_local(1, coef_f, pd, 0);

    overall_converged = false;
    pass = 0;
    while pass < max_outer_passes
        pass = pass + 1;

        if pass > 1
            F_now = (coef_f.')*K;
            gamma_pts = refresh_gamma_local(F_now, phi, phi_0, cone_rad, L, fast_peaks);
            pd = compute_pass_data_local(gamma_pts,x,y,k0,kappa_phi0,coef_K_phi0,P_V,L);
        end

        pass_start_iter   (end+1) = iter + 1;        %#ok<AGROW>
        pass_gamma_pts    {end+1} = pd.gamma_pts;    %#ok<AGROW>
        pass_coef_hstar   {end+1} = pd.coef_hstar;   %#ok<AGROW>
        pass_h_star_norm  (end+1) = pd.h_star_norm;  %#ok<AGROW>
        pass_q_rate_upper (end+1) = pd.q_rate_upper; %#ok<AGROW>
        pass_c_Gamma_lower(end+1) = pd.c_Gamma_lower;%#ok<AGROW>

        if verbose
            fprintf('Pass %d: M=%d, ||h*||=%.4g, c_Gamma>=%.4g, q<=%.4g, starting at iter %d\n', ...
                pass, pd.M, pd.h_star_norm, pd.c_Gamma_lower, pd.q_rate_upper, iter+1);
        end

        % Inner loop
        while iter < Max_iter
            f_g = (coef_f.') * pd.Kappa_gam;
            [worst,jmax] = max(abs(f_g));

            F_now = (coef_f.')*K;
            Fmag_max = max(abs(F_now));
            cur_max_sample_dB = 10*log10(worst.^2 / Fmag_max^2);
            if cur_max_sample_dB <= eps_dB
                if verbose
                    fprintf('  Pass %d inner-converged at iter %d (sample-max %.2f dB <= %.2f dB).\n', ...
                        pass, iter, cur_max_sample_dB, eps_dB);
                end
                break;
            end

            scalar     = f_g(jmax) / pd.M_norm_sq(jmax);
            delta_coef = -scalar * pd.coef_M_gam(:, jmax);
            coef_f     = coef_f + delta_coef;

            iter = iter + 1;
            decrement_store(iter+1) = abs(f_g(jmax)).^2 / pd.M_norm_sq(jmax);

            ns = ns + 1;
            A_store{ns}     = delta_coef;
            A_eff_store{ns} = coef_f;
            phi_store(ns)   = pd.gamma_pts(jmax);

            record_iter_local(iter+1, coef_f, pd, pass);

            if verbose
                fprintf('  P%d I%d: theta=%.4f, |f|=%.4g, decr=%.4g, ||h-h*||=%.4g, dense-max=%.2f dB\n', ...
                    pass, iter, pd.gamma_pts(jmax), abs(f_g(jmax)), ...
                    decrement_store(iter+1), distance_to_fstar_store(iter+1), ...
                    dense_max_sidelobe_store(iter+1));
            end

            if show_plots
                plot_pattern_v5(phi,(coef_f.')*K, ...
                    'label',sprintf('Pass %d, iter %d',pass,iter), ...
                    'phi_0',phi_0,'phi_s',pd.gamma_pts,'show_plots',true,'iter',iter);
            end
        end

        % Outer stop test
        F_now = (coef_f.')*K;
        pkdB = dense_peak_dB_local(F_now, phi, phi_0, cone_rad, fast_peaks);
        if isnan(pkdB) || pkdB <= eps_dB
            overall_converged = true;
            if verbose
                fprintf('Pass %d: dense-mesh max sidelobe %.2f dB <= %.2f dB. OVERALL DONE.\n', ...
                    pass, pkdB, eps_dB);
            end
            break;
        end
        if iter >= Max_iter
            if verbose
                fprintf('Iteration budget (%d) exhausted in pass %d. Dense-mesh max sidelobe = %.2f dB > %.2f dB.\n', ...
                    Max_iter, pass, pkdB, eps_dB);
            end
            break;
        end
        if verbose
            fprintf('Pass %d: dense-mesh max sidelobe %.2f dB > %.2f dB. Refreshing Gamma.\n', ...
                pass, pkdB, eps_dB);
        end
    end

    if ~overall_converged && iter < Max_iter && pass >= max_outer_passes
        warning(['Reached max_outer_passes (%d) without dense-mesh ' ...
                 'convergence. The intrinsic Chebyshev floor for L=%d may be above eps_dB=%.2f dB.'], ...
                 max_outer_passes, L, eps_dB);
    end

    F_total    = (coef_f.')*K;
    F_star     = ((coef_K_phi0 + pd.coef_hstar).')*K;
    Fmag       = abs(F_total);
    F_at_phi_0 = (coef_f.')*kappa_phi0;

    if fast_peaks
        [peakVals,peakLocs] = findpeaks_fast(Fmag,phi);
    else
        [peakVals,peakLocs] = findpeaks_circular(Fmag,phi);
    end
    if ~isempty(peakVals)
        d_main = abs(atan2(sin(peakLocs - phi_0), cos(peakLocs - phi_0)));
        [~,mainIdx] = min(d_main);
        Big_phi_final = peakLocs(mainIdx);
        Big_Val_final = peakVals(mainIdx);
        peakVals(mainIdx) = []; peakLocs(mainIdx) = [];
        if isempty(peakVals)
            Slobe_fin=[]; phi_s_fin=[];
        else
            peakVals_db = 10*log10((peakVals.^2) / max(Fmag).^2);
            [Slobe_fin,sortIx] = sort(peakVals_db,'descend');
            phi_s_fin = peakLocs(sortIx);
        end
    else
        Big_phi_final = phi_0; Big_Val_final = abs(F_at_phi_0);
        Slobe_fin = []; phi_s_fin = [];
    end

    if show_plots || show_final_plot
        plot_pattern_v5(phi, F_total, ...
            'label','Final Plot: Constrained Perturbative Method', ...
            'phi_0',phi_0,'phi_s',phi_s_fin,'Slobe',Slobe_fin, ...
            'iter',iter,'show_plots',true,'cone_rad',cone_rad,'Big_phi',Big_phi_final);
    end

    A_store=A_store(1:ns); A_eff_store=A_eff_store(1:ns); phi_store=phi_store(1:ns);

    % ---- Pack results ----
    results.method = 'constrained_v2';
    results.fast_peaks = fast_peaks;
    results.final_iteration = iter; results.final_epoch = iter;
    results.total_time = toc;
    results.focus_angle = phi_0; results.focus_angle_deg = round(rad2deg(phi_0));
    results.cone_rad = cone_rad;
    results.null_angle = []; results.null_angle_deg = [];

    results.overall_converged = overall_converged;
    results.num_passes = pass; results.max_outer_passes = max_outer_passes;
    results.pass_start_iter = pass_start_iter;
    results.pass_gamma_pts = pass_gamma_pts;
    results.pass_coef_hstar = pass_coef_hstar;
    results.pass_h_star_norm = pass_h_star_norm;
    results.pass_q_rate_upper = pass_q_rate_upper;
    results.pass_c_Gamma_lower = pass_c_Gamma_lower;
    results.pass_idx_store = pass_idx_store;

    results.gamma_pts = pd.gamma_pts;
    results.M = pd.M; results.L = L;
    results.coef_K_phi0 = coef_K_phi0;
    results.coef_hstar = pd.coef_hstar;
    results.coef_f = coef_f;
    results.h_star_norm = pd.h_star_norm;
    results.q_rate_upper = pd.q_rate_upper;
    results.c_Gamma_lower = pd.c_Gamma_lower;
    results.M_norm_sq = pd.M_norm_sq;

    results.decrement_store = decrement_store;
    results.distance_to_fstar_store = distance_to_fstar_store;
    results.max_sidelobe_store = max_sidelobe_store;
    results.dense_max_sidelobe_store = dense_max_sidelobe_store;
    results.dense_max_phi_store = dense_max_phi_store;
    results.directivity_metric_1_beamwidth_store = directivity_metric_1_beamwidth_store;
    results.focus_value_store = abs(focus_value_store);
    results.focus_value_store_dB = focus_value_store_dB;
    results.fstar_function = F_star;
    results.final_function = F_total;
    results.F_at_phi_0 = abs(F_at_phi_0);

    results.A_store = A_store; results.A_eff_store = A_eff_store; results.phi_store = phi_store;
    results.A_eff = coef_f; results.delta_eff = zeros(L,1);
    results.x_pos = x; results.y_pos = y;
    results.phi_s_fin = phi_s_fin;
    results.Big_phi_final = Big_phi_final; results.Big_Val_final = Big_Val_final;
    results.initial_m = pd.M; results.m = pd.M;

    if return_funcs
        results.F_store = F_store; results.G2D_store = G2D_store; results.G3D_store = G3D_store;
    end


    % ============== nested helpers (closure capture is needed) ==============
    function record_iter_local(idx, coef_now, pdL, pass_id)
        F_local = (coef_now.')*K;
        Fmag_loc = abs(F_local);
        F_at_0  = (coef_now.')*kappa_phi0;

        focus_value_store(idx)    = F_at_0;
        focus_value_store_dB(idx) = 10*log10(abs(F_at_0).^2 / max(Fmag_loc).^2);

        f_g = (coef_now.') * pdL.Kappa_gam;
        if pdL.M > 0
            mv = max(abs(f_g));
            max_sidelobe_store(idx) = 10*log10(mv.^2 / max(Fmag_loc).^2);
        end

        [pkdB, pkphi] = dense_peak_dB_local(F_local, phi, phi_0, cone_rad, fast_peaks);
        dense_max_sidelobe_store(idx) = pkdB;
        dense_max_phi_store(idx)      = pkphi;

        h_now = coef_now - coef_K_phi0;
        distance_to_fstar_store(idx) = sqrt(real( (h_now - pdL.coef_hstar)' * (h_now - pdL.coef_hstar) ));

        pass_idx_store(idx) = pass_id;

        if return_funcs
            bw = directivity_met_v2(phi, F_local, phi_0);
            directivity_metric_1_beamwidth_store(idx) = bw.beamwidth;
            F_store(idx, :) = F_local;
            G2D_store(idx)  = local_gain2D(F_local, phi, phi_0);
            G3D_store(idx)  = local_gain3D(phi, theta_mesh, coef_now, x, y, z, k0, phi_0, theta_0);
        end
    end
end


function pd = compute_pass_data_local(gpts, x, y, k0, kappa_phi0, coef_K_phi0, P_V, L)
    gpts = mod(gpts(:),2*pi);
    Mloc = numel(gpts);
    Kappa_gam = exp(1j*k0*(x*cos(gpts.') + y*sin(gpts.')));   % L x Mloc
    Kalpha_at_phi0 = (Kappa_gam') * kappa_phi0;
    Kphi0_at_gamma = (coef_K_phi0.') * Kappa_gam;
    coef_M_gam = conj(Kappa_gam) - conj(kappa_phi0) * (Kalpha_at_phi0.' / L);
    M_norm_sq  = L - (abs(Kalpha_at_phi0).^2)/L;
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
    sv = svd(E_onV);
    if isempty(sv)
        sigma_min_E = 0;
    else
        sv_keep = sv(sv > 1e-10*max(sv));
        if isempty(sv_keep), sigma_min_E = 0; else, sigma_min_E = min(sv_keep); end
    end
    c_Gamma_lower = sigma_min_E / sqrt(max(Mloc,1));
    q_rate_upper  = sqrt(max(0, 1 - c_Gamma_lower^2 / L));
    pd = struct('gamma_pts',gpts,'M',Mloc,'Kappa_gam',Kappa_gam, ...
        'coef_M_gam',coef_M_gam,'M_norm_sq',M_norm_sq,'coef_hstar',coef_hstar, ...
        'h_star_norm',h_star_norm,'c_Gamma_lower',c_Gamma_lower,'q_rate_upper',q_rate_upper);
end


function gpts = refresh_gamma_local(F_now, phi, phi_0, cone_rad, L, fast_peaks)
    if fast_peaks
        [pv,pl] = findpeaks_fast(abs(F_now),phi);
    else
        [pv,pl] = findpeaks_circular(abs(F_now),phi);
    end
    if isempty(pv)
        gpts = mod(phi_0 + linspace(2*pi/L, 2*pi - 2*pi/L, L-1).', 2*pi); return;
    end
    d_main = abs(atan2(sin(pl - phi_0), cos(pl - phi_0)));
    [~,im] = min(d_main);
    pv(im) = []; pl(im) = [];
    if ~isempty(cone_rad) && ~isempty(pl)
        d = mod(pl - phi_0 + pi, 2*pi) - pi;
        keep = abs(d) > cone_rad;
        pv = pv(keep); pl = pl(keep);
    end
    if isempty(pv)
        gpts = mod(phi_0 + linspace(2*pi/L, 2*pi - 2*pi/L, L-1).', 2*pi); return;
    end
    [~,ix] = sort(pv,'descend');
    ntake = min(L-1, numel(ix));
    gpts = mod(pl(ix(1:ntake)), 2*pi);
end


function [pkdB, pkphi] = dense_peak_dB_local(F_local, phi, phi_0, cone_rad, fast_peaks)
    Fmag = abs(F_local);
    if fast_peaks
        [pv,pl] = findpeaks_fast(Fmag,phi);
    else
        [pv,pl] = findpeaks_circular(Fmag,phi);
    end
    if isempty(pv), pkdB=NaN; pkphi=NaN; return; end
    d_main = abs(atan2(sin(pl - phi_0), cos(pl - phi_0)));
    [~,im] = min(d_main);
    pv(im) = []; pl(im) = [];
    if ~isempty(cone_rad) && ~isempty(pl)
        d = mod(pl - phi_0 + pi, 2*pi) - pi;
        keep = abs(d) > cone_rad;
        pv = pv(keep); pl = pl(keep);
    end
    if isempty(pv), pkdB = -Inf; pkphi = NaN; return; end
    [pkmag,ix] = max(pv);
    pkdB  = 10*log10(pkmag.^2 / max(Fmag).^2);
    pkphi = pl(ix);
end


function G = local_gain2D(F_total, phi, phi_0)
    phi = phi(:).';
    I  = trapz(phi, abs(F_total).^2, 2);
    F0 = interp1(phi, F_total.', phi_0, 'linear','extrap').';
    G  = 10*log10((abs(F0).^2 * 4*pi)./I);
end


function G = local_gain3D(phi, theta_mesh, A, x, y, z, k0, phi_0, theta_0)
    if isempty(z), z = zeros(size(A)); end
    A=A(:); x=x(:); y=y(:); z=z(:);
    phi=phi(:).'; theta=theta_mesh(:);
    L=numel(theta); Mp=numel(phi);
    F = zeros(L,Mp);
    % In-plane phase matrix is theta-independent: hoist it out of the loop.
    B = x*cos(phi) + y*sin(phi);    % NxMp
    has_z = any(z ~= 0);
    for li = 1:L
        sT = sin(theta(li)); cT = cos(theta(li));
        if has_z, ph = k0*(sT*B + z*cT); else, ph = (k0*sT)*B; end
        E  = cos((pi/2)*cT)/sT; if ~isfinite(E), E=0; end
        F(li,:) = (A.')*exp(1j*ph)*E;
    end
    Pw = abs(F).^2 .* sin(theta);
    Itot = trapz(theta, trapz(phi, Pw, 2));
    F0 = interp2(phi, theta, F, phi_0, theta_0, 'linear', 0);
    G  = 10*log10((abs(F0)^2 * 4*pi)/Itot);
end
