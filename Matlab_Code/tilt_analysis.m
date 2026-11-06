%% Tilt analysis
%  1. Run a beamforming method once on the ideal (1+octagon) layout to obtain
%     the optimized complex currents A_eff.
%  2. For a sweep of tilt angles, rotate the element positions with
%         yz tilt: rotation about the x-axis  (R_x(alpha))
%         xz tilt: rotation about the y-axis  (R_y(beta))
%     and recompute the horizontal-plane (theta = pi/2) pattern using the
%     same A_eff (currents do not change when the drone tilts).
%  3. Report the largest tilt angle in each case such that the worst
%     sidelobe is still below threshold_dB (default -20 dB).
%  4. If a null direction is specified, also track the null level and report
%     the largest tilt angle such that the null stays below null_threshold_dB.
%
%  Note: a literal in-plane xy rotation would be a pure heading change
%  about z and would not create a true tilt. For convenience, the
%  xz tilt is exposed with both xz and xy field aliases in the
%  output struct so the live script can use either naming convention.
%
%  'method' name-value selects the optimizer:
%       'v24'         (default)   perturb_method_v24
%       'v23'                     perturb_method_v23
%       'constrained'             perturb_method_constrained_v2
%       'constrained_v1'          perturb_method_constrained_v1
%
%  Dependencies: the chosen method, d1d2Convert.m, findpeaks_fast.m,
%                findpeaks_circular.m.

function res = tilt_analysis(varargin)

    p = inputParser;
    addParameter(p, 'N',                9,       @(v) mod(v,2)==1 && v>=3);
    addParameter(p, 'd_ideal',          0.04880, @isnumeric);
    addParameter(p, 'phi_0',            0,       @isnumeric);
    addParameter(p, 'null_phi',         [],      @isnumeric);
    addParameter(p, 'Max_iter',         60,      @isnumeric);
    addParameter(p, 'eps_dB',           -20,     @isnumeric);
    addParameter(p, 'threshold_dB',     -20,     @isnumeric);
    addParameter(p, 'null_threshold_dB', -20,    @isnumeric);
    addParameter(p, 'angle_deg_list',   linspace(0, 60, 61), @isnumeric);
    addParameter(p, 'verbose',          false,   @islogical);
    addParameter(p, 'method',           'v24',   @(s) ischar(s) || isstring(s));
    addParameter(p, 'cone_rad',         [],      @isnumeric);
    addParameter(p, 'max_outer_passes', 50,      @isnumeric);
    addParameter(p, 'fast_peaks',       true,    @islogical);
    addParameter(p, 'show_plots',       true,    @islogical);
    parse(p, varargin{:});
    a = p.Results;

    method_key = lower(string(a.method));
    use_null = ~(isempty(a.null_phi) || any(isnan(a.null_phi)));
    if use_null && any(method_key == ["constrained", "constrained_v1"])
        error('tilt_analysis: method "%s" does not support null_phi.', a.method);
    end

    phi_0 = mod(a.phi_0, 2*pi);
    null_phi = mod(a.null_phi, 2*pi);

    freq = 3e9; lambda = 3e8/freq; k0 = 2*pi/lambda;

    [x0, y0] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    z0 = zeros(size(x0));

    % Optimize currents on the ideal layout with the selected method.
    switch method_key
        case "v24"
            opt_args = {a.Max_iter, a.eps_dB, x0(:), y0(:), phi_0, ...
                        'fast_peaks', a.fast_peaks, ...
                        'verbose', false, ...
                        'show_plots', false, ...
                        'show_final_plot', false, ...
                        'return_funcs', false, ...
                        'full_loop', false};
            if use_null
                opt_args = [opt_args, {'null_phi', null_phi}]; %#ok<AGROW>
            end
            opt = perturb_method_v24(opt_args{:});

        case "v23"
            opt_args = {a.Max_iter, a.eps_dB, x0(:), y0(:), phi_0, ...
                        'verbose', false, ...
                        'show_plots', false, ...
                        'show_final_plot', false, ...
                        'return_funcs', false, ...
                        'full_loop', false};
            if use_null
                opt_args = [opt_args, {'null_phi', null_phi}]; %#ok<AGROW>
            end
            opt = perturb_method_v23(opt_args{:});

        case "constrained"
            cone = a.cone_rad;
            if isempty(cone), cone = deg2rad(30); end
            opt = perturb_method_constrained_v2(a.Max_iter, a.eps_dB, x0(:), y0(:), phi_0, ...
                'cone_rad', cone, 'max_outer_passes', a.max_outer_passes, ...
                'fast_peaks', a.fast_peaks, ...
                'verbose', false, 'show_final_plot', false, 'return_funcs', false);

        case "constrained_v1"
            cone = a.cone_rad;
            if isempty(cone), cone = deg2rad(30); end
            opt = perturb_method_constrained_v1(a.Max_iter, a.eps_dB, x0(:), y0(:), phi_0, ...
                'cone_rad', cone, 'max_outer_passes', a.max_outer_passes, ...
                'verbose', false, 'show_final_plot', false, 'return_funcs', false);

        otherwise
            error('tilt_analysis: unknown method "%s".', a.method);
    end
    A_eff = opt.A_eff(:);

    angles = a.angle_deg_list(:);
    nA = numel(angles);

    [worst_yz, best_yz, gain_yz, null_yz_dB] = deal(nan(nA,1));
    [worst_xz, best_xz, gain_xz, null_xz_dB] = deal(nan(nA,1));

    pts0 = [x0(:).'; y0(:).'; z0(:).'];

    for i = 1:nA
        alpha = deg2rad(angles(i));
        ca = cos(alpha);
        sa = sin(alpha);

        % yz tilt: rotation about x-axis
        Rx = [1 0 0; 0 ca -sa; 0 sa ca];
        pts = Rx * pts0;
        [worst_yz(i), best_yz(i), gain_yz(i), null_yz_dB(i)] = ...
            compute_metrics(pts(1,:), pts(2,:), A_eff, phi_0, null_phi, use_null, k0, a.fast_peaks);

        % xz tilt: rotation about y-axis
        Ry = [ca 0 sa; 0 1 0; -sa 0 ca];
        pts = Ry * pts0;
        [worst_xz(i), best_xz(i), gain_xz(i), null_xz_dB(i)] = ...
            compute_metrics(pts(1,:), pts(2,:), A_eff, phi_0, null_phi, use_null, k0, a.fast_peaks);

        if a.verbose && mod(i, 10) == 0
            if use_null
                fprintf(['  angle=%.1f deg: yz worst=%.2f dB, xz worst=%.2f dB, ' ...
                         'yz null=%.2f dB, xz null=%.2f dB\n'], ...
                    angles(i), worst_yz(i), worst_xz(i), null_yz_dB(i), null_xz_dB(i));
            else
                fprintf('  angle=%.1f deg: yz worst=%.2f dB, xz worst=%.2f dB\n', ...
                    angles(i), worst_yz(i), worst_xz(i));
            end
        end
    end

    thr_yz = find_threshold_angle(angles, worst_yz, a.threshold_dB);
    thr_xz = find_threshold_angle(angles, worst_xz, a.threshold_dB);

    if use_null
        null_thr_yz = find_threshold_angle(angles, null_yz_dB, a.null_threshold_dB);
        null_thr_xz = find_threshold_angle(angles, null_xz_dB, a.null_threshold_dB);
    else
        null_thr_yz = NaN;
        null_thr_xz = NaN;
    end

    res.angle_deg_list     = angles;
    res.focus_angle        = phi_0;
    res.focus_angle_deg    = rad2deg(phi_0);
    res.null_angle         = [];
    res.null_angle_deg     = [];
    if use_null
        res.null_angle     = null_phi;
        res.null_angle_deg = rad2deg(null_phi);
    end

    res.worst_yz = worst_yz; res.best_yz = best_yz; res.gain_yz = gain_yz;
    res.worst_xz = worst_xz; res.best_xz = best_xz; res.gain_xz = gain_xz;
    res.worst_xy = worst_xz; res.best_xy = best_xz; res.gain_xy = gain_xz;
    res.null_yz_dB = null_yz_dB;
    res.null_xz_dB = null_xz_dB;
    res.null_xy_dB = null_xz_dB;
    res.max_tilt_yz_deg = thr_yz;
    res.max_tilt_xz_deg = thr_xz;
    res.max_tilt_xy_deg = thr_xz;
    res.max_tilt_null_yz_deg = null_thr_yz;
    res.max_tilt_null_xz_deg = null_thr_xz;
    res.max_tilt_null_xy_deg = null_thr_xz;
    res.threshold_dB      = a.threshold_dB;
    res.null_threshold_dB = a.null_threshold_dB;
    res.A_eff             = A_eff;
    res.lambda            = lambda;
    res.params            = a;

    fprintf('Focus angle = %.1f deg\n', res.focus_angle_deg);
    fprintf('Max tilt with WS <= %.0f dB:  yz = %.2f deg,  xz = %.2f deg.\n', ...
        a.threshold_dB, thr_yz, thr_xz);
    if use_null
        fprintf('Null angle = %.1f deg\n', res.null_angle_deg);
        fprintf('Max tilt with null <= %.0f dB:  yz = %.2f deg,  xz = %.2f deg.\n', ...
            a.null_threshold_dB, null_thr_yz, null_thr_xz);
    end

    if ~a.show_plots
        return;
    end

    col_yz = [0.00 0.45 0.74];
    col_xz = [0.85 0.33 0.10];
    meta_label = sprintf('Focus = %.1f deg', res.focus_angle_deg);
    if use_null
        meta_label = sprintf('%s   |   Null = %.1f deg', meta_label, res.null_angle_deg);
    end

    figure('Name', 'Tilt: worst sidelobe', 'Color', 'w', ...
           'Position', [100 100 980 560]);
    hold on;
    plot(angles, worst_yz, '-o', 'Color', col_yz, 'LineWidth', 2.2, ...
         'MarkerSize', 5, 'MarkerFaceColor', col_yz);
    plot(angles, worst_xz, '-s', 'Color', col_xz, 'LineWidth', 2.2, ...
         'MarkerSize', 5, 'MarkerFaceColor', col_xz);
    yline(a.threshold_dB, '--', sprintf('%.0f dB threshold', a.threshold_dB), ...
          'Color', [0.20 0.20 0.20], 'LineWidth', 1.4, ...
          'LabelHorizontalAlignment', 'left');
    if ~isnan(thr_yz)
        xline(thr_yz, ':', sprintf('YZ limit = %.1f deg', thr_yz), ...
              'Color', col_yz, 'LineWidth', 1.6, 'LabelOrientation', 'horizontal');
    end
    if ~isnan(thr_xz)
        xline(thr_xz, ':', sprintf('XZ limit = %.1f deg', thr_xz), ...
              'Color', col_xz, 'LineWidth', 1.6, 'LabelOrientation', 'horizontal');
    end
    xlabel('Tilt angle [deg]');
    ylabel('Worst sidelobe [dB]');
    title('Worst sidelobe vs tilt angle');
    style_axes(gca);
    legend({'YZ tilt (about x)', 'XZ tilt (about y)'}, ...
           'Location','southoutside', 'Orientation','horizontal', 'Box', 'off');
    add_meta_text(meta_label);

    figure('Name', 'Tilt: best sidelobe', 'Color', 'w', ...
           'Position', [130 130 980 560]);
    hold on;
    plot(angles, best_yz, '-o', 'Color', col_yz, 'LineWidth', 2.2, ...
         'MarkerSize', 5, 'MarkerFaceColor', col_yz);
    plot(angles, best_xz, '-s', 'Color', col_xz, 'LineWidth', 2.2, ...
         'MarkerSize', 5, 'MarkerFaceColor', col_xz);
    xlabel('Tilt angle [deg]');
    ylabel('Best sidelobe [dB]');
    title('Best sidelobe vs tilt angle');
    style_axes(gca);
    legend({'YZ tilt (about x)', 'XZ tilt (about y)'}, ...
           'Location','southoutside', 'Orientation','horizontal', 'Box', 'off');
    add_meta_text(meta_label);

    figure('Name', 'Tilt: gain @ phi_0', 'Color', 'w', ...
           'Position', [160 160 980 560]);
    hold on;
    plot(angles, gain_yz, '-o', 'Color', col_yz, 'LineWidth', 2.2, ...
         'MarkerSize', 5, 'MarkerFaceColor', col_yz);
    plot(angles, gain_xz, '-s', 'Color', col_xz, 'LineWidth', 2.2, ...
         'MarkerSize', 5, 'MarkerFaceColor', col_xz);
    xlabel('Tilt angle [deg]');
    ylabel('Main-beam gain at \phi_0 [dB]');
    title('Main-beam gain vs tilt angle');
    style_axes(gca);
    legend({'YZ tilt (about x)', 'XZ tilt (about y)'}, ...
           'Location','southoutside', 'Orientation','horizontal', 'Box', 'off');
    add_meta_text(meta_label);

    if use_null
        figure('Name', 'Tilt: null level', 'Color', 'w', ...
               'Position', [190 190 980 560]);
        hold on;
        plot(angles, null_yz_dB, '-o', 'Color', col_yz, 'LineWidth', 2.2, ...
             'MarkerSize', 5, 'MarkerFaceColor', col_yz);
        plot(angles, null_xz_dB, '-s', 'Color', col_xz, 'LineWidth', 2.2, ...
             'MarkerSize', 5, 'MarkerFaceColor', col_xz);
        yline(a.null_threshold_dB, '--', sprintf('%.0f dB null threshold', a.null_threshold_dB), ...
              'Color', [0.20 0.20 0.20], 'LineWidth', 1.4, ...
              'LabelHorizontalAlignment', 'left');
        if ~isnan(null_thr_yz)
            xline(null_thr_yz, ':', sprintf('YZ null limit = %.1f deg', null_thr_yz), ...
                  'Color', col_yz, 'LineWidth', 1.6, 'LabelOrientation', 'horizontal');
        end
        if ~isnan(null_thr_xz)
            xline(null_thr_xz, ':', sprintf('XZ null limit = %.1f deg', null_thr_xz), ...
                  'Color', col_xz, 'LineWidth', 1.6, 'LabelOrientation', 'horizontal');
        end
        xlabel('Tilt angle [deg]');
        ylabel('Null level [dB]');
        title('Null retention vs tilt angle');
        style_axes(gca);
        legend({'YZ tilt (about x)', 'XZ tilt (about y)'}, ...
               'Location','southoutside', 'Orientation','horizontal', 'Box', 'off');
        add_meta_text(meta_label);
    end
end


function [worst, best, gain, null_level_dB] = compute_metrics(x, y, A, phi_0, null_phi, use_null, k0, fast_peaks)
    phi = linspace(0, 2*pi, 1001);
    phi(end) = [];
    A = A(:);
    x = x(:);
    y = y(:);
    phase = k0 * (x * cos(phi) + y * sin(phi));   % theta = pi/2
    F = A.' * exp(1j * phase);
    Fmag = abs(F);

    if fast_peaks
        [pv, pl] = findpeaks_fast(Fmag, phi);
    else
        [pv, pl] = findpeaks_circular(Fmag, phi);
    end

    if isempty(pv)
        worst = NaN;
        best = NaN;
    else
        dphi = abs(atan2(sin(pl - phi_0), cos(pl - phi_0)));
        [~, im] = min(dphi);
        pv(im) = [];
        if isempty(pv)
            worst = NaN;
            best = NaN;
        else
            sl_dB = 10*log10((pv.^2) / (max(Fmag).^2));
            worst = max(sl_dB);
            best  = min(sl_dB);
        end
    end

    I = trapz(phi, Fmag.^2);
    F0 = interp1(phi, F, phi_0, 'linear', 'extrap');
    gain = 10*log10((abs(F0).^2 * 4*pi) / I);

    null_level_dB = NaN;
    if use_null
        Fn = interp1(phi, F, null_phi, 'linear', 'extrap');
        null_level_dB = 10*log10((abs(Fn).^2) / (max(Fmag).^2));
    end
end


function thr = find_threshold_angle(angles, metric, threshold_dB)
    idx = find(metric > threshold_dB, 1, 'first');
    if isempty(idx)
        thr = max(angles);
    elseif idx == 1
        thr = 0;
    else
        a1 = angles(idx-1);
        a2 = angles(idx);
        m1 = metric(idx-1);
        m2 = metric(idx);
        thr = a1 + (threshold_dB - m1) * (a2 - a1) / (m2 - m1);
    end
end


function style_axes(ax)
    ax.FontSize = 13;
    ax.LineWidth = 1.1;
    ax.Box = 'on';
    ax.GridAlpha = 0.16;
    ax.MinorGridAlpha = 0.10;
    ax.XMinorGrid = 'on';
    ax.YMinorGrid = 'on';
    grid(ax, 'on');
end


function add_meta_text(meta_label)
    annotation('textbox', [0.13 0.93 0.75 0.05], ...
        'String', meta_label, ...
        'EdgeColor', 'none', ...
        'HorizontalAlignment', 'center', ...
        'FontSize', 12, ...
        'FontWeight', 'bold', ...
        'Color', [0.15 0.15 0.15]);
end
