function results = perturb_method_2_beam_v6(varargin)
%PERTURB_METHOD_2_BEAM_V6  Audited + optimized rewrite of v5. Same outputs.
%   Hot-path optimizations:
%     - Precomputed kernel K = exp(i*k0*(x*cos(phi)+y*sin(phi))); F = (A_eff.')*K
%     - Direct (A_eff.')*steer evaluation at phi_s replaces interp1
%     - phase_ps cached: steer = exp(1j*phase_ps); delta_corr = -phase_ps
%     - F_total recomputed once per epoch, not once per correction
%       (matters when full_loop=true with many sidelobes)
%     - 'fast_peaks' (default true) selects findpeaks_fast vs findpeaks_circular
%
%   Beamwidths (both foci):
%     The FINAL pattern's half-power (-3 dB) beamwidth is always computed
%     for BOTH foci and returned in
%       .beamwidth_1, .beamwidth_2           (rad; NaN if no -3 dB crossing)
%       .beamwidth_1_deg, .beamwidth_2_deg   (deg)
%       .bw1_left_05, .bw1_right_05          (rad, edge angles in [0,2*pi))
%       .bw2_left_05, .bw2_right_05
%     Per-iteration histories .directivity_metric_1_beamwidth_store_1/2
%     still require 'return_funcs', true.
%
%     Convention: each beam's width is measured relative to that beam's
%     OWN peak value, NOT the global pattern max (directivity_met_v2's
%     convention) -- the global normalization returns garbage/NaN for the
%     weaker of two beams. Same convention as combined_2beam_metrics.
%     The beamwidth helper is vectorized and toolbox-free, so the
%     per-iteration histories no longer call findpeaks.
%
%   Final metrics (same field set as Crammer_Simultaneous_Constraints and
%   combined_2beam_metrics, so testbed tables can consume any solver
%   interchangeably):
%       .final_gain2D_1, .final_gain2D_2          (always computed)
%       .final_gain3D_1, .final_gain3D_2          (NaN unless
%           'final_metrics', true -- full 3D pattern integration is by
%           far the most expensive step, so benchmark loops can skip it;
%           same gating convention as Crammer_Simultaneous_Constraints)
%       .main_beam_angle_final_1/2                 (rad)
%       .main_beam_skew_final_1/2 (+_deg, +_signed, +_signed_deg)
%       .final_max_sidelobe_dB, .final_max_sidelobe_phi(_deg)
%           (-Inf / NaN when the two main beams are the only peaks)
%
%   Fixes vs the previous v5:
%     - History stores no longer overwrite the initial-state sample
%       (index 1 = state before the first correction; index k+1 = state
%       after epoch k) and are preallocated to their true maximum length
%       (the old code silently grew them past Max_iter).
%     - scan_2beam's nearest-peak-to-focus selection is wrap-aware, so a
%       focus at/near 0 deg no longer grabs the wrong main beam when the
%       true peak sits just below 2*pi.

    p = inputParser; p.FunctionName = 'perturb_method_2_beam_v6';
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
    addParameter(p,'final_metrics',false,@islogical);
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

    % History stores: index 1 holds the initial state (before any
    % correction); index k+1 holds the state after epoch k. The loop runs
    % epochs iter = 0..Max_iter, so the largest written index is
    % Max_iter+2.
    tic; iter = 0;
    nan1 = nan(Max_iter+2,1);
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
    if ~isempty(Slobe)
        max_sidelobe_store(1)=Slobe(1); max_side_phi_store(1)=phi_s(1);
    end

    if return_funcs
        Fmag_now = abs(F_total);
        directivity_metric_1_beamwidth_store_1(1) = halfpower_bw(Fmag_now,phi,Big_phi_1,Big_Val_1);
        directivity_metric_1_beamwidth_store_2(1) = halfpower_bw(Fmag_now,phi,Big_phi_2,Big_Val_2);
    end

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

            if show_plots
                F_add = (A_corr_scalar * conj(steer_t).') * K;
                plot_pattern_v5(phi,F_add,'label',"Plot of Correction Pattern (Step 12: 'f_{cor}')", ...
                    'phi_0',ps,'iter',iter,'show_plots',true);
            end
        end

        % One pattern evaluation per epoch; the corrections above only
        % need (A_eff.')*steer_t, never the full F_total.
        F_total = (A_eff.')*K;

        if show_plots || show_plots_st12
            plot_pattern_v5(phi,F_total,'label',"Plot of Corrected Pattern (Step 12: 'f_{new}')", ...
                'phi_0',[phi_0_1 phi_0_2],'iter',iter,'show_plots',true);
        end

        [Slobe,phi_s,Big_phi_1,Big_Val_1,Big_phi_2,Big_Val_2,Fmag_max] = ...
            scan_2beam(F_total,phi,phi_0_1,phi_0_2,eps_dB,cone_rad,fast_peaks);

        main_peakLoc_store_1(iter+2)=Big_phi_1; main_peakVal_store_1(iter+2)=Big_Val_1;
        main_peakLoc_store_2(iter+2)=Big_phi_2; main_peakVal_store_2(iter+2)=Big_Val_2;
        main_peak_skew_1(iter+2) = phi_0_1 - Big_phi_1;
        main_peak_skew_2(iter+2) = phi_0_2 - Big_phi_2;
        focus_value_store_1(iter+2) = (A_eff.')*kappa_phi01;
        focus_value_store_2(iter+2) = (A_eff.')*kappa_phi02;

        if return_funcs
            Fmag_now = abs(F_total);
            directivity_metric_1_beamwidth_store_1(iter+2) = halfpower_bw(Fmag_now,phi,Big_phi_1,Big_Val_1);
            directivity_metric_1_beamwidth_store_2(iter+2) = halfpower_bw(Fmag_now,phi,Big_phi_2,Big_Val_2);
        end

        if ~isempty(Slobe)
            max_sidelobe_store(iter+2)=Slobe(1); max_side_phi_store(iter+2)=phi_s(1);
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

    % ---- Final half-power beamwidths at both foci (always computed) ----
    Fmag_fin = abs(F_total);
    [bw1, bw1_l, bw1_r] = halfpower_bw(Fmag_fin, phi, Big_phi_final_1, Big_Val_final_1);
    [bw2, bw2_l, bw2_r] = halfpower_bw(Fmag_fin, phi, Big_phi_final_2, Big_Val_final_2);
    results.beamwidth_1     = bw1;
    results.beamwidth_2     = bw2;
    results.beamwidth_1_deg = rad2deg(bw1);
    results.beamwidth_2_deg = rad2deg(bw2);
    results.bw1_left_05     = bw1_l;
    results.bw1_right_05    = bw1_r;
    results.bw2_left_05     = bw2_l;
    results.bw2_right_05    = bw2_r;

    % ---- Final metrics: gains, skews, max sidelobe ----
    % 2D gains: cheap (trapz over the existing pattern, exact focus
    % values already in F_at_phi_0_*), always computed.
    I2 = trapz(phi, abs(F_total).^2, 2);
    results.final_gain2D_1 = 10*log10((F_at_phi_0_1.^2 * 4*pi) / I2);
    results.final_gain2D_2 = 10*log10((F_at_phi_0_2.^2 * 4*pi) / I2);

    % 3D gains: require integrating the full 3D pattern (M theta-cuts of
    % an NxM field each) -- by far the most expensive step in this file,
    % so they are only computed on request ('final_metrics', true).
    if a.final_metrics
        if isempty(a.z), zv = zeros(N,1); else, zv = a.z(:); end
        theta_mesh = linspace(0, pi, M).';
        F3D = local_F3D(phi, theta_mesh, A_eff, x, y, zv, k0);
        I3 = trapz(theta_mesh, trapz(phi, abs(F3D).^2 .* sin(theta_mesh), 2));
        F0_3d_1 = local_F3D_point(phi_0_1, a.theta_0, A_eff, x, y, zv, k0);
        F0_3d_2 = local_F3D_point(phi_0_2, a.theta_0, A_eff, x, y, zv, k0);
        results.final_gain3D_1 = 10*log10((abs(F0_3d_1)^2 * 4*pi) / I3);
        results.final_gain3D_2 = 10*log10((abs(F0_3d_2)^2 * 4*pi) / I3);
    else
        results.final_gain3D_1 = NaN;
        results.final_gain3D_2 = NaN;
    end

    % Main-beam skews: wrap-aware angular distance between each focus and
    % its actual final main-beam peak.
    d1s = phi_0_1 - Big_phi_final_1;
    d2s = phi_0_2 - Big_phi_final_2;
    results.main_beam_angle_final_1           = Big_phi_final_1;
    results.main_beam_angle_final_2           = Big_phi_final_2;
    results.main_beam_skew_final_1_signed     = atan2(sin(d1s), cos(d1s));
    results.main_beam_skew_final_2_signed     = atan2(sin(d2s), cos(d2s));
    results.main_beam_skew_final_1_signed_deg = rad2deg(results.main_beam_skew_final_1_signed);
    results.main_beam_skew_final_2_signed_deg = rad2deg(results.main_beam_skew_final_2_signed);
    results.main_beam_skew_final_1            = abs(results.main_beam_skew_final_1_signed);
    results.main_beam_skew_final_2            = abs(results.main_beam_skew_final_2_signed);
    results.main_beam_skew_final_1_deg        = rad2deg(results.main_beam_skew_final_1);
    results.main_beam_skew_final_2_deg        = rad2deg(results.main_beam_skew_final_2);

    % Final max sidelobe: Slobe_fin came from the final scan with
    % eps_dB=-inf and no cone, so every peak except the two main beams is
    % a candidate, already sorted descending. -Inf means the main beams
    % were the only peaks (matches combined_2beam_metrics).
    if isempty(Slobe_fin)
        results.final_max_sidelobe_dB      = -Inf;
        results.final_max_sidelobe_phi     = NaN;
        results.final_max_sidelobe_phi_deg = NaN;
    else
        results.final_max_sidelobe_dB      = Slobe_fin(1);
        results.final_max_sidelobe_phi     = phi_s_fin(1);
        results.final_max_sidelobe_phi_deg = rad2deg(phi_s_fin(1));
    end
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
    % Wrap-aware nearest peak: plain |pl - phi_0| misselects when the
    % focus and its peak straddle the 0/2*pi seam.
    [~,i1] = min(abs(atan2(sin(pl - phi_0_1), cos(pl - phi_0_1))));
    Bphi1 = pl(i1); Bval1 = pv(i1);
    pv(i1) = []; pl(i1) = [];
    if isempty(pv)
        Slobe=[]; phi_s=[]; Bphi2=NaN; Bval2=NaN; return;
    end
    [~,i2] = min(abs(atan2(sin(pl - phi_0_2), cos(pl - phi_0_2))));
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


function [bwv, left05, right05] = halfpower_bw(Fmag, phi, pk_phi, pk_val)
%HALFPOWER_BW  Vectorized circular -3 dB beamwidth of one lobe.
%   Measured relative to the lobe's OWN peak value pk_val (not the global
%   pattern max). Walks outward from the mesh point nearest pk_phi in
%   both directions via index rotation + find(...,1), interpolating the
%   crossing angle linearly. Returns NaN if the pattern never drops below
%   pk_val/sqrt(2) (beams merged into one broad lobe), or if pk_phi or
%   pk_val is NaN. Same convention as combined_2beam_metrics.
    if isnan(pk_phi) || isnan(pk_val) || pk_val <= 0
        bwv = NaN; left05 = NaN; right05 = NaN; return;
    end
    Fmag = Fmag(:).'; phi = phi(:).';
    M = numel(Fmag);
    thr = pk_val / sqrt(2);
    [~,i0] = min(abs(atan2(sin(phi - pk_phi), cos(phi - pk_phi))));
    right05 = halfpower_crossing(Fmag, phi, [i0:M 1:i0-1],     thr, +1);
    left05  = halfpower_crossing(Fmag, phi, [i0:-1:1 M:-1:i0+1], thr, -1);
    if isnan(left05) || isnan(right05)
        bwv = NaN;
    else
        bwv = mod(right05 - left05, 2*pi);
    end
end


function ang = halfpower_crossing(Fmag, phi, ord, thr, dirn)
    w = Fmag(ord);
    j = find(w < thr, 1);
    if isempty(j) || j == 1
        ang = NaN; return;
    end
    iA = ord(j-1); iB = ord(j);
    pA = phi(iA); pB = phi(iB);
    if dirn > 0 && pB < pA
        pB = pB + 2*pi;     % stepped across the 2*pi seam
    elseif dirn < 0 && pB > pA
        pB = pB - 2*pi;
    end
    ang = mod(pA + (thr - Fmag(iA)) * (pB - pA) / (Fmag(iB) - Fmag(iA)), 2*pi);
end


function F3D = local_F3D(phi_loc, theta_loc, A_loc, x_loc, y_loc, z_loc, k0_loc)
    % Includes the cos((pi/2)*cos(theta))/sin(theta) half-wave-dipole
    % element factor, matching gain_calc_3D in perturb_method_v25 /
    % Crammer_Simultaneous_Constraints and combined_2beam_metrics. The
    % in-plane phase matrix B is theta-independent, so it is hoisted out
    % of the loop.
    A_loc = A_loc(:);
    x_loc = x_loc(:); y_loc = y_loc(:); z_loc = z_loc(:);
    phi_loc = phi_loc(:).';
    theta_loc = theta_loc(:);
    L = numel(theta_loc);
    Mp = numel(phi_loc);
    F3D = zeros(L, Mp);
    B = x_loc*cos(phi_loc) + y_loc*sin(phi_loc);   % NxMp
    has_z = any(z_loc ~= 0);
    for li = 1:L
        sT = sin(theta_loc(li));
        cT = cos(theta_loc(li));
        E = cos((pi/2) * cT) / sT;
        if ~isfinite(E) || E == 0
            continue;   % element factor kills this cut; row stays zero
        end
        if has_z
            ph = (k0_loc*sT)*B + (k0_loc*cT)*z_loc;
        else
            ph = (k0_loc*sT)*B;
        end
        F3D(li, :) = (A_loc.') * exp(1j * ph) * E;
    end
end


function F0 = local_F3D_point(phi0, theta0, A_loc, x_loc, y_loc, z_loc, k0_loc)
    % Exact single-point evaluation of the 3D field (same element-factor
    % convention as local_F3D), so foci between mesh points are never
    % interpolated.
    sT = sin(theta0);
    cT = cos(theta0);
    E = cos((pi/2) * cT) / sT;
    if ~isfinite(E)
        F0 = 0;
        return;
    end
    ph = k0_loc * (x_loc(:)*(sT*cos(phi0)) + y_loc(:)*(sT*sin(phi0)) + z_loc(:)*cT);
    F0 = (A_loc(:).' * exp(1j * ph)) * E;
end
