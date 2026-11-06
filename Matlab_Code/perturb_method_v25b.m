function results = perturb_method_v24(varargin)
%PERTURB_METHOD_V24  Heavily optimized rewrite of v23. Same external API.
%   Hot-path optimizations:
%     - Precomputed kernel K = exp(i*k0*(x*cos(phi)+y*sin(phi))); F = A_eff.'*K
%     - Direct (A_eff.')*steer evaluation at phi_s replaces interp1
%     - phase_ps cached: steer = exp(1j*phase_ps); delta_corr = -phase_ps
%     - Branch-free A_eff update: A_eff += scalar * conj(steer)  (no A_corr_vec build)
%     - directivity_met_v2 is called only if return_funcs=true
%     - 3D gain computed only if return_funcs=true
%     - Pre-sized cell stores; no end+1 growth
%     - 'fast_peaks' (default true) selects findpeaks_fast over findpeaks_circular
%
%   Dependencies: findpeaks_fast or findpeaks_circular, plot_pattern_v5,
%                 directivity_met_v2 (only used if return_funcs).

    p = inputParser; p.FunctionName = 'perturb_method_v24';
    addRequired (p,'Max_iter',@isnumeric); addRequired(p,'eps_dB',@isnumeric);
    addRequired (p,'x',@isnumeric); addRequired(p,'y',@isnumeric);
    addRequired (p,'phi_0',@isnumeric);
    addOptional (p,'z',[],@isnumeric); addOptional(p,'A_init',[],@isnumeric);
    addOptional (p,'null_phi',[],@isnumeric);
    addOptional (p,'show_plots',false,@islogical);
    addOptional (p,'show_plot_raw',false,@islogical);
    addOptional (p,'show_plot_init',false,@islogical);
    addOptional (p,'show_plots_st7',false,@islogical);
    addOptional (p,'show_plots_st12',false,@islogical);
    addOptional (p,'show_plots_st16',false,@islogical);
    addOptional (p,'show_final_plot',false,@islogical);
    addOptional (p,'verbose',false,@islogical);
    addOptional (p,'full_loop',false,@islogical);
    addOptional (p,'const_null_update',false,@islogical);
    addParameter(p,'cone_rad',[],@isnumeric);
    addOptional (p,'return_funcs',false,@islogical);
    addOptional (p,'theta_0',pi*0.5,@isnumeric);
    addParameter(p,'fast_peaks',true,@islogical);   % NEW
    parse(p,varargin{:}); a = p.Results;

    Max_iter=a.Max_iter; eps_dB=a.eps_dB;
    x=a.x(:); y=a.y(:); z=a.z(:); N=numel(x);
    if N<2, error('x,y must contain at least two elements.'); end
    phi_0   = mod(a.phi_0,2*pi);
    theta_0 = mod(a.theta_0,2*pi);
    null_phi= mod(a.null_phi,2*pi);
    cone_rad=a.cone_rad; verbose=a.verbose; full_loop=a.full_loop;
    return_funcs=a.return_funcs; fast_peaks=a.fast_peaks;
    use_null = ~(isempty(null_phi) || any(isnan(null_phi)));

    k0 = 2*pi*3e9/3e8;
    center_idx = 1; outer_idx = 2:N;

    M = 1000;
    phi = linspace(0,2*pi,M+1); phi(end)=[];

    % Precomputed kernel K (NxM): F = A_eff.' * K
    K = exp(1j*k0*(x*cos(phi) + y*sin(phi)));

    % Initial amplitudes
    if ~isempty(a.A_init)
        if use_null
            if numel(a.A_init)~=N-1, error('Null version: A_init length must be N-1.'); end
            A0 = [0; a.A_init(:)];
        else
            if numel(a.A_init)~=N,   error('Non-Null version: A_init length must be N.'); end
            A0 = a.A_init(:);
        end
    else
        A0 = ones(N,1); if use_null, A0(center_idx)=0; end
    end

    if a.show_plots || a.show_plot_raw
        plot_pattern_v5(phi,(A0.')*K,'label',"Raw Geometric Pattern (No Beam Directing)", ...
            'show_plots',true,'iter',-1);
    end

    % Cache steering vectors that are reused every iteration.
    kappa_phi0 = exp(1j*k0*(x*cos(phi_0)+y*sin(phi_0)));        % Nx1
    if use_null
        kappa_null = exp(1j*k0*(x*cos(null_phi)+y*sin(null_phi)));
    else
        kappa_null = [];   %#ok<NASGU>
    end

    delta0 = -k0*(x*cos(phi_0) + y*sin(phi_0));
    A_eff  = A0 .* exp(1j*delta0);

    tic; iter = 0;

    nan1 = nan(Max_iter+1,1);
    max_sidelobe_store=nan1; max_side_phi_store=nan1;
    main_peakLoc_store=nan1; main_peakVal_store=nan1;
    focus_value_store=nan1; focus_value_store_dB=nan1;
    main_peak_skew=nan1;
    directivity_metric_1_beamwidth_store=nan1;
    G2D_store=nan(Max_iter+1,numel(phi_0));
    G3D_store=nan(Max_iter+1,numel(phi_0));

    cap = (Max_iter+2)*max(N,2) + 4;
    A_store     = cell(1,cap); A_store{1}=A0;
    delta_store = cell(1,cap); delta_store{1}=delta0;
    A_eff_store = cell(1,cap); A_eff_store{1}=A_eff;
    phi_store   = nan(1,cap);  phi_store(1)=phi_0;
    ns = 1;

    if return_funcs
        F_store = nan(Max_iter+1,M);
        theta_mesh = linspace(0,pi,M);
    end

    % Initial pattern + scan
    F_total = (A_eff.')*K;

    if a.show_plots || a.show_plot_init
        plot_pattern_v5(phi,F_total,'label',"Initial Pattern (with Focus)(Step 3)", ...
            'phi_0',phi_0,'show_plots',true);
    end

    if return_funcs
        F_store(1,:) = F_total;
        G2D_store(1) = local_gain2D(F_total,phi,phi_0);
        G3D_store(1) = local_gain3D(phi,theta_mesh,A_eff,x,y,z,k0,phi_0,theta_0);
        bw0 = directivity_met_v2(phi,F_total,phi_0);
        directivity_metric_1_beamwidth_store(1) = bw0.beamwidth;
    end

    [Slobe,phi_s,mainLoc,mainVal,Fmag_max] = scan_sl(F_total,phi,phi_0,eps_dB,cone_rad,fast_peaks);
    F_at_phi0 = (A_eff.')*kappa_phi0;
    main_peakLoc_store(1)=mainLoc; main_peakVal_store(1)=mainVal;
    main_peak_skew(1)=atan2(sin(phi_0-mainLoc),cos(phi_0-mainLoc));
    focus_value_store(1)=F_at_phi0;
    focus_value_store_dB(1)=10*log10(abs(F_at_phi0)^2/Fmag_max^2);
    if ~isempty(Slobe)
        max_sidelobe_store(1)=Slobe(1); max_side_phi_store(1)=phi_s(1);
    end
    initial_m = numel(Slobe); m = initial_m;
    if verbose, fprintf('Found %d initial sidelobes above %.1f dB.\n',m,eps_dB); end

    if a.show_plots || a.show_plots_st7
        plot_pattern_v5(phi,F_total,'label',"Pattern prior to While Loop (Step 7)", ...
            'phi_0',phi_0,'phi_s',phi_s,'Slobe',Slobe,'show_plots',true,'Big_phi',mainLoc);
    end

    % ---- Main loop ----
    while m>0 && iter<=Max_iter
        if verbose, fprintf('iter = %d\n',iter); end
        if full_loop, m_epoch = m; else, m_epoch = 1; end

        for t = 1:m_epoch
            ps = phi_s(t);
            phase_ps = k0*(x*cos(ps) + y*sin(ps));     % Nx1
            steer_t  = exp(1j*phase_ps);                % Nx1
            F_at = (A_eff.')*steer_t;                   % scalar (exact)

            if use_null
                A_corr_scalar = -F_at/(N-1);
                contrib = A_corr_scalar * conj(steer_t); contrib(center_idx)=0;
                A_eff = A_eff + contrib;
                A_corr_vec = zeros(N,1); A_corr_vec(outer_idx)=A_corr_scalar;
            else
                A_corr_scalar = -F_at/N;
                A_eff = A_eff + A_corr_scalar * conj(steer_t);
                A_corr_vec = A_corr_scalar * ones(N,1);
            end
            delta_corr = -phase_ps;

            ns = ns+1;
            A_store{ns}=A_corr_vec; delta_store{ns}=delta_corr;
            phi_store(ns)=ps; A_eff_store{ns}=A_eff;

            F_total = (A_eff.')*K;

            if return_funcs
                F_store(iter+1,:)=F_total;
                G2D_store(iter+1)=local_gain2D(F_total,phi,phi_0);
                G3D_store(iter+1)=local_gain3D(phi,theta_mesh,A_eff,x,y,z,k0,phi_0,theta_0);
            end

            if a.show_plots
                F_add = (A_corr_vec.') * (exp(1j*delta_corr) .* K);
                plot_pattern_v5(phi,F_add,'label',"Plot of Correction Pattern (Step 12: 'f_{cor}')", ...
                    'phi_0',ps,'iter',iter,'show_plots',true);
            end
        end

        iter = iter + 1;

        if (~use_null) && (a.show_plots || a.show_plots_st12)
            plot_pattern_v5(phi,F_total,'label',"Plot of Corrected Pattern (Step 12: 'f_{new}')", ...
                'phi_0',phi_0,'iter',iter,'show_plots',true);
        end

        % Optional null update each epoch
        if use_null && a.const_null_update
            phase_n   = k0*(x(center_idx)*cos(null_phi) + y(center_idx)*sin(null_phi));
            steer_full= kappa_null;
            F_at_N = (A_eff.')*steer_full;
            A_null_vec = zeros(N,1); A_null_vec(center_idx) = -F_at_N;
            delta_null_vec = zeros(N,1); delta_null_vec(center_idx) = -phase_n;
            A_eff = A_eff + A_null_vec .* exp(1j*delta_null_vec);
            ns = ns+1;
            A_store{ns}=A_null_vec; delta_store{ns}=delta_null_vec; A_eff_store{ns}=A_eff;
            F_total = (A_eff.')*K;
            if return_funcs
                F_store(iter+1,:)=F_total;
                G2D_store(iter+1)=local_gain2D(F_total,phi,phi_0);
                G3D_store(iter+1)=local_gain3D(phi,theta_mesh,A_eff,x,y,z,k0,phi_0,theta_0);
            end
        end

        % Re-scan
        [Slobe,phi_s,mainLoc,mainVal,Fmag_max] = scan_sl(F_total,phi,phi_0,eps_dB,cone_rad,fast_peaks);
        F_at_phi0 = (A_eff.')*kappa_phi0;
        main_peakLoc_store(iter+1)=mainLoc;
        main_peakVal_store(iter+1)=mainVal;
        main_peak_skew(iter+1)=atan2(sin(phi_0-mainLoc),cos(phi_0-mainLoc));
        focus_value_store(iter+1)=F_at_phi0;
        focus_value_store_dB(iter+1)=10*log10(abs(F_at_phi0)^2/Fmag_max^2);
        if return_funcs
            bw = directivity_met_v2(phi,F_total,phi_0);
            directivity_metric_1_beamwidth_store(iter+1) = bw.beamwidth;
        end
        if ~isempty(Slobe)
            max_sidelobe_store(iter+1)=Slobe(1);
            max_side_phi_store(iter+1)=phi_s(1);
        end
        m = numel(Slobe);
        if verbose, fprintf('After Iteration %d: %d sidelobes above %.1f dB\n',iter,m,eps_dB); end

        if a.show_plots || a.show_plots_st16
            plot_pattern_v5(phi,F_total,'label',"Plot of Corrected Pattern (Step 16: 'f_{new}')", ...
                'phi_0',phi_0,'phi_s',phi_s,'Slobe',Slobe,'null_phi',null_phi, ...
                'iter',iter,'show_plots',true,'Big_phi',mainLoc);
        end
    end

    % Final scan
    [Slobe_fin,phi_s_fin,Big_phi_final,Big_Val_final] = scan_sl(F_total,phi,phi_0,-inf,[],fast_peaks);
    F_at_phi_0 = (A_eff.')*kappa_phi0;

    % Optional null synthesis (basic)
    if use_null && ~a.const_null_update
        phase_n    = k0*(x(center_idx)*cos(null_phi) + y(center_idx)*sin(null_phi));
        steer_full = kappa_null;
        F_at_N = (A_eff.')*steer_full;
        A_null_vec = zeros(N,1); A_null_vec(center_idx) = -F_at_N;
        delta_null_vec = zeros(N,1); delta_null_vec(center_idx) = -phase_n;
        A_eff = A_eff + A_null_vec .* exp(1j*delta_null_vec);
        ns = ns+1;
        A_store{ns}=A_null_vec; delta_store{ns}=delta_null_vec; A_eff_store{ns}=A_eff;
        F_total = (A_eff.')*K;
        [Slobe_fin,phi_s_fin,Big_phi_final,Big_Val_final] = scan_sl(F_total,phi,phi_0,-inf,[],fast_peaks);
        F_at_phi_0 = (A_eff.')*kappa_phi0;
    end

    if a.show_plots || a.show_final_plot
        if use_null && a.const_null_update
            lbl="Final Plot: 1-Beam-1-Null (Const. update) Method"; itlbl=iter-1;
        elseif use_null
            lbl="Final Plot: 1-Beam-1-Null (Basic Method)(Step 19)"; itlbl=iter+1;
        else
            lbl="Final Plot: 1-Beam-0-Null Method";                  itlbl=iter;
        end
        plot_pattern_v5(phi,F_total,'label',lbl,'phi_0',phi_0, ...
            'phi_s',phi_s_fin,'Slobe',Slobe_fin,'null_phi',null_phi, ...
            'iter',itlbl,'show_plots',true,'cone_rad',cone_rad,'Big_phi',Big_phi_final);
    end

    A_store=A_store(1:ns); delta_store=delta_store(1:ns);
    A_eff_store=A_eff_store(1:ns); phi_store=phi_store(1:ns);
    delta_eff = zeros(size(A_eff));

    % Pack outputs (matches v23 fields)
    results.final_epoch = iter; results.final_iteration = iter;
    results.total_time  = toc;   results.m = m;
    results.focus_angle = phi_0; results.focus_angle_deg = round(rad2deg(phi_0));
    results.cone_rad    = cone_rad;
    results.fast_peaks  = fast_peaks;
    if use_null
        results.null_angle = null_phi; results.null_angle_deg = round(rad2deg(null_phi));
    else
        results.null_angle = []; results.null_angle_deg = [];
    end
    if return_funcs
        results.F_store = F_store; results.G2D_store = G2D_store; results.G3D_store = G3D_store;
    end
    results.max_sidelobe_store = max_sidelobe_store;
    results.max_side_phi_store = max_side_phi_store;
    results.main_peakLoc_store = main_peakLoc_store;
    results.main_peakVal_store = main_peakVal_store;
    results.main_peak_skew     = main_peak_skew;
    results.directivity_metric_1_beamwidth_store = directivity_metric_1_beamwidth_store;
    results.final_function = F_total;
    results.phi_s_sorted_fin = phi_s_fin;
    results.phi_s_fin        = phi_s_fin;
    results.Big_Val_final    = Big_Val_final;
    results.Big_phi_final    = Big_phi_final;
    results.F_at_phi_0       = abs(F_at_phi_0);
    results.focus_value_store    = abs(focus_value_store);
    results.focus_value_store_dB = abs(focus_value_store_dB);
    results.A_store=A_store; results.A_eff_store=A_eff_store;
    results.delta_store=delta_store; results.phi_store=phi_store;
    results.A_eff=A_eff; results.delta_eff=delta_eff;
    results.x_pos=x; results.y_pos=y;
    results.initial_m = initial_m;
    results.final_gain2D = local_gain2D(F_total,phi,phi_0);
    if return_funcs
        results.final_gain3D = local_gain3D(phi,theta_mesh,A_eff,x,y,z,k0,phi_0,theta_0);
    else
        results.final_gain3D = NaN;
    end
end


function [Slobe,phi_s,mainLoc,mainVal,Fmag_max] = scan_sl(F_total,phi,phi_0,eps_dB,cone_rad,fast_peaks)
    Fmag = abs(F_total);
    Fmag_max = max(Fmag);
    if fast_peaks
        [pv,pl] = findpeaks_fast(Fmag,phi);
    else
        [pv,pl] = findpeaks_circular(Fmag,phi);
    end
    if isempty(pv), mainLoc=NaN; mainVal=NaN; Slobe=[]; phi_s=[]; return; end
    pl = mod(pl,2*pi);
    [~,im] = min(abs(atan2(sin(pl-phi_0),cos(pl-phi_0))));
    mainLoc=pl(im); mainVal=pv(im);
    pv(im)=[]; pl(im)=[];
    if isempty(pv), Slobe=[]; phi_s=[]; return; end
    pv_db = 10*log10((pv.^2)/(Fmag_max^2));
    if isempty(cone_rad)
        mask = pv_db > eps_dB;
    else
        sd = mod(pl - phi_0 + pi, 2*pi) - pi;
        mask = (pv_db > eps_dB) & (abs(sd) > cone_rad);
    end
    Slobe = pv_db(mask); phi_s = pl(mask);
    [Slobe,idx] = sort(Slobe,'descend'); phi_s = phi_s(idx);
end


function G = local_gain2D(F_total,phi,phi_0)
    phi = phi(:).';
    I  = trapz(phi,abs(F_total).^2,2);
    F0 = interp1(phi,F_total.',phi_0,'linear','extrap').';
    G  = 10*log10((abs(F0).^2 * 4*pi)./I);
end


function G = local_gain3D(phi,theta_mesh,A,x,y,z,k0,phi_0,theta_0)
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
    Itot = trapz(theta,trapz(phi,Pw,2));
    F0 = interp2(phi,theta,F,phi_0,theta_0,'linear',0);
    G  = 10*log10((abs(F0)^2 * 4*pi)/Itot);
end
