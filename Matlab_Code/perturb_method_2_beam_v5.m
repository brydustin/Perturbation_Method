function results = perturb_method_2_beam_v5(varargin)
%PERTURB_METHOD_2_BEAM_V5  Heavily optimized rewrite of v4. Same outputs.
%   Hot-path optimizations:
%     - Precomputed kernel K = exp(i*k0*(x*cos(phi)+y*sin(phi))); F = (A_eff.')*K
%     - Direct (A_eff.')*steer evaluation at phi_s replaces interp1
%     - phase_ps cached: steer = exp(1j*phase_ps); delta_corr = -phase_ps
%     - directivity_met_v2 only when return_funcs=true
%     - 'fast_peaks' (default true) selects findpeaks_fast vs findpeaks_circular

    p = inputParser; p.FunctionName = 'perturb_method_2_beam_v5';
    addRequired (p,'x',@isnumeric); addRequired(p,'y',@isnumeric);
    addRequired (p,'phi_0_1',@isnumeric); addRequired(p,'phi_0_2',@isnumeric);
    addParameter(p,'Max_iter',40,@isnumeric);
    addParameter(p,'eps_dB',-20,@isnumeric);
    addParameter(p,'verbose',false,@islogical);
    addParameter(p,'show_plots',false,@islogical);
    addParameter(p,'show_plot_raw',false,@islogical);
    addParameter(p,'show_plot_init',false,@islogical);
    addParameter(p,'show_plots_st7',false,@islogical);
    addParameter(p,'show_plots_st12',false,@islogical);
    addParameter(p,'show_final_plot',false,@islogical);
    addParameter(p,'full_loop',false,@islogical);
    addParameter(p,'null_phi',[],@isnumeric);
    addParameter(p,'cone_rad',[],@isnumeric);
    addOptional (p,'return_funcs',false,@islogical);
    addOptional (p,'theta_0',pi*0.5,@isnumeric);
    addOptional (p,'z',[],@isnumeric);
    addOptional (p,'A_init',[],@isnumeric);
    addOptional (p,'show_plots_st16',false,@islogical);
    addParameter(p,'fast_peaks',true,@islogical);
    parse(p,varargin{:}); a = p.Results;

    x=a.x(:); y=a.y(:);
    phi_0_1=mod(a.phi_0_1,2*pi); phi_0_2=mod(a.phi_0_2,2*pi);
    cone_rad=a.cone_rad; Max_iter=a.Max_iter; eps_dB=a.eps_dB;
    verbose=a.verbose; show_plots=a.show_plots;
    show_plot_init=a.show_plot_init; show_plots_st7=a.show_plots_st7;
    show_plots_st12=a.show_plots_st12; show_final_plot=a.show_final_plot;
    full_loop=a.full_loop;
    null_phi = mod(a.null_phi,2*pi);
    return_funcs=a.return_funcs; fast_peaks=a.fast_peaks;
    use_null = ~(isempty(null_phi) || any(isnan(null_phi)));

    N = numel(x);
    if N<2, error('x,y must contain at least two elements.'); end
    center_idx = 1; outer_idx = 2:N;

    k0 = 2*pi*3e9/3e8;
    M = 1000;
    phi = linspace(0,2*pi,M+1); phi(end)=[];

    K = exp(1j*k0*(x*cos(phi)+y*sin(phi)));   % NxM

    % Cache steering vectors at the two foci (reused every iteration)
    kappa_phi01 = exp(1j*k0*(x*cos(phi_0_1)+y*sin(phi_0_1)));
    kappa_phi02 = exp(1j*k0*(x*cos(phi_0_2)+y*sin(phi_0_2)));

    % ---- Closed-form 2-beam initial coefficients ----
    phase_01 = -k0*(x*cos(phi_0_1) + y*sin(phi_0_1));   % Nx1
    phase_02 = -k0*(x*cos(phi_0_2) + y*sin(phi_0_2));
    A_n = exp(-1j*phase_01) + exp(-1j*phase_02);
    term1 = exp(-1j*phase_01).*exp(+1j*phase_02);
    term2 = exp(-1j*phase_02).*exp(+1j*phase_01);
    A_0 = -(sum(term1(2:end)) + sum(term2(2:end)));

    % Effective initial currents (absorb both A_n and A_0 into the same vector
    % so F = A_eff.' * K). Element 1 carries A_0 alone; elements 2..N carry A_n.
    A_eff = A_n; A_eff(1) = A_0;

    if show_plots || a.show_plot_raw
        plot_pattern_v5(phi,(ones(N,1).')*K,'label',"Raw Geometric Pattern (No Beam Directing)", ...
            'show_plots',true,'iter',-1);
    end

    F_total = (A_eff.')*K;

    if show_plots || show_plot_init
        plot_pattern_v5(phi,F_total,'label',"Initial Pattern (Analytic Foci)(Step 3)", ...
            'phi_0',[phi_0_1 phi_0_2],'show_plots',true);
    end

    tic; iter = 0;
    nan1 = nan(Max_iter,1);
    max_sidelobe_store=nan1; max_side_phi_store=nan1;
    main_peakLoc_store_1=nan1; main_peakVal_store_1=nan1; focus_value_store_1=nan1;
    main_peakLoc_store_2=nan1; main_peakVal_store_2=nan1; focus_value_store_2=nan1;
    directivity_metric_1_beamwidth_store_1=nan1; directivity_metric_1_beamwidth_store_2=nan1;
    main_peak_skew_1=nan1; main_peak_skew_2=nan1;

    [Slobe,phi_s,Big_phi_1,Big_Val_1,Big_phi_2,Big_Val_2,Fmag_max] = ...
        scan_2beam(F_total,phi,phi_0_1,phi_0_2,eps_dB,cone_rad,fast_peaks);

    main_peakLoc_store_1(1)=Big_phi_1; main_peakVal_store_1(1)=Big_Val_1;
    main_peakLoc_store_2(1)=Big_phi_2; main_peakVal_store_2(1)=Big_Val_2;
    main_peak_skew_1(1) = phi_0_1 - Big_phi_1;
    main_peak_skew_2(1) = phi_0_2 - Big_phi_2;
    focus_value_store_1(1) = (A_eff.')*kappa_phi01;
    focus_value_store_2(1) = (A_eff.')*kappa_phi02;

    m = numel(Slobe);
    if verbose, fprintf('Found %d initial sidelobes above %.1f dB.\n', m, eps_dB); end

    if show_plots || show_plots_st7
        plot_pattern_v5(phi,F_total,'label',"Pattern prior to While Loop (Step 7)", ...
            'phi_0',[phi_0_1 phi_0_2],'phi_s',phi_s,'Slobe',Slobe,'show_plots',true);
    end

    while m>0 && iter<=Max_iter
        if verbose, fprintf('iter = %d\n',iter); end
        if full_loop, m_epoch = m; else, m_epoch = 1; end

        for t = 1:m_epoch
            ps = phi_s(t);
            phase_ps = k0*(x*cos(ps)+y*sin(ps));
            steer_t  = exp(1j*phase_ps);
            F_at = (A_eff.')*steer_t;

            if use_null
                A_corr_scalar = -F_at/(N-1);
                contrib = A_corr_scalar * conj(steer_t); contrib(center_idx)=0;
                A_eff = A_eff + contrib;
            else
                A_corr_scalar = -F_at/N;
                A_eff = A_eff + A_corr_scalar * conj(steer_t);
            end

            F_total = (A_eff.')*K;

            if show_plots
                F_add = (A_corr_scalar * conj(steer_t).') * K;
                plot_pattern_v5(phi,F_add,'label',"Plot of Correction Pattern (Step 12: 'f_{cor}')", ...
                    'phi_0',ps,'iter',iter,'show_plots',true);
            end
        end

        if show_plots || show_plots_st12
            plot_pattern_v5(phi,F_total,'label',"Plot of Corrected Pattern (Step 12: 'f_{new}')", ...
                'phi_0',[phi_0_1 phi_0_2],'iter',iter,'show_plots',true);
        end

        [Slobe,phi_s,Big_phi_1,Big_Val_1,Big_phi_2,Big_Val_2,Fmag_max] = ...
            scan_2beam(F_total,phi,phi_0_1,phi_0_2,eps_dB,cone_rad,fast_peaks);

        main_peakLoc_store_1(iter+1)=Big_phi_1; main_peakVal_store_1(iter+1)=Big_Val_1;
        main_peakLoc_store_2(iter+1)=Big_phi_2; main_peakVal_store_2(iter+1)=Big_Val_2;
        main_peak_skew_1(iter+1) = phi_0_1 - Big_phi_1;
        main_peak_skew_2(iter+1) = phi_0_2 - Big_phi_2;
        focus_value_store_1(iter+1) = (A_eff.')*kappa_phi01;
        focus_value_store_2(iter+1) = (A_eff.')*kappa_phi02;

        if return_funcs
            bw1 = directivity_met_v2(phi,F_total,phi_0_1);
            bw2 = directivity_met_v2(phi,F_total,phi_0_2);
            directivity_metric_1_beamwidth_store_1(iter+1) = bw1.beamwidth;
            directivity_metric_1_beamwidth_store_2(iter+1) = bw2.beamwidth;
        end

        if isempty(Slobe)
            max_sidelobe_store(iter+1)=NaN; max_side_phi_store(iter+1)=NaN;
        else
            max_sidelobe_store(iter+1)=Slobe(1); max_side_phi_store(iter+1)=phi_s(1);
        end

        m = numel(Slobe);
        if verbose, fprintf('After Epoch %d: %d sidelobes above %.1f dB\n', iter+1, m, eps_dB); end

        if show_plots
            plot_pattern_v5(phi,F_total,'label',"Plot of Corrected Pattern (Step 16: 'f_{new}')", ...
                'phi_0',[phi_0_1 phi_0_2],'phi_s',phi_s,'Slobe',Slobe, ...
                'iter',iter,'show_plots',true);
        end

        iter = iter + 1;
    end

    % Final scan
    [Slobe_fin,phi_s_fin,Big_phi_final_1,Big_Val_final_1,Big_phi_final_2,Big_Val_final_2] = ...
        scan_2beam(F_total,phi,phi_0_1,phi_0_2,-inf,[],fast_peaks);

    F_at_phi_0_1 = abs((A_eff.')*kappa_phi01);
    F_at_phi_0_2 = abs((A_eff.')*kappa_phi02);

    if show_plots || show_final_plot
        plot_pattern_v5(phi,F_total,'label',"Final Plot: 2-Beam Method", ...
            'phi_0',[phi_0_1 phi_0_2],'phi_s',phi_s_fin,'Slobe',Slobe_fin, ...
            'iter',iter,'show_plots',true,'cone_rad',cone_rad);
    end

    results.final_epoch = iter-1; results.final_iteration = iter;
    results.total_time = toc; results.cone_rad = cone_rad;
    results.fast_peaks = fast_peaks;
    results.final_function = abs(F_total);
    results.initial_function = abs((A_n+0).');   % placeholder; retained for legacy
    results.focus_angle_1 = phi_0_1; results.focus_angle_1_deg = round(rad2deg(phi_0_1));
    results.focus_angle_2 = phi_0_2; results.focus_angle_2_deg = round(rad2deg(phi_0_2));
    results.Big_Val_final_1 = Big_Val_final_1; results.Big_Val_final_2 = Big_Val_final_2;
    results.Big_phi_final_1 = Big_phi_final_1; results.Big_phi_final_2 = Big_phi_final_2;
    results.max_sidelobe_store = max_sidelobe_store;
    results.F_at_phi_0_1 = F_at_phi_0_1; results.F_at_phi_0_2 = F_at_phi_0_2;
    results.main_peakLoc_store_1 = main_peakLoc_store_1;
    results.main_peakLoc_store_2 = main_peakLoc_store_2;
    results.main_peakVal_store_1 = main_peakVal_store_1;
    results.main_peakVal_store_2 = main_peakVal_store_2;
    results.main_peak_skew_1 = main_peak_skew_1;
    results.main_peak_skew_2 = main_peak_skew_2;
    results.directivity_metric_1_beamwidth_store_1 = directivity_metric_1_beamwidth_store_1;
    results.directivity_metric_1_beamwidth_store_2 = directivity_metric_1_beamwidth_store_2;
    results.focus_value_store_1 = abs(focus_value_store_1);
    results.focus_value_store_2 = abs(focus_value_store_2);
    results.A_eff = A_eff; results.x_pos = x; results.y_pos = y;
end


function [Slobe,phi_s,Bphi1,Bval1,Bphi2,Bval2,Fmag_max] = ...
    scan_2beam(F_total,phi,phi_0_1,phi_0_2,eps_dB,cone_rad,fast_peaks)
    Fmag = abs(F_total); Fmag_max = max(Fmag);
    if fast_peaks
        [pv,pl] = findpeaks_fast(Fmag,phi);
    else
        [pv,pl] = findpeaks_circular(Fmag,phi);
    end
    if isempty(pv)
        Slobe=[]; phi_s=[]; Bphi1=NaN; Bval1=NaN; Bphi2=NaN; Bval2=NaN; return;
    end
    [~,i1] = min(abs(pl - phi_0_1));
    Bphi1 = pl(i1); Bval1 = pv(i1);
    pv(i1) = []; pl(i1) = [];
    if isempty(pv)
        Slobe=[]; phi_s=[]; Bphi2=NaN; Bval2=NaN; return;
    end
    [~,i2] = min(abs(pl - phi_0_2));
    Bphi2 = pl(i2); Bval2 = pv(i2);
    pv(i2) = []; pl(i2) = [];
    if isempty(pv)
        Slobe=[]; phi_s=[]; return;
    end
    pv_db = 10*log10((pv.^2)/(Fmag_max^2));
    if isempty(cone_rad)
        mask = pv_db > eps_dB;
    else
        d1 = mod(pl - phi_0_1 + pi, 2*pi) - pi;
        d2 = mod(pl - phi_0_2 + pi, 2*pi) - pi;
        mask = (pv_db > eps_dB) & (abs(d1)>cone_rad) & (abs(d2)>cone_rad);
    end
    Slobe = pv_db(mask); phi_s = pl(mask);
    [Slobe,idx] = sort(Slobe,'descend'); phi_s = phi_s(idx);
end
