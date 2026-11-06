function res = focus_angle_sweep_2beam(varargin)
%FOCUS_ANGLE_SWEEP_2BEAM  Movie sweep for the Advanced 2-Beam method.
%   Two foci are kept at a fixed angular separation `sep_deg`. The first
%   focus phi_1 sweeps across angle_deg_list (default 0:1:359); the second
%   tracks at phi_2 = mod(phi_1 + sep, 2*pi). At each angle the full
%   perturb_method_2_beam_v5 algorithm runs to convergence and only the
%   FINAL pattern is captured for that frame.
%
%   Required name-value parameter
%     'sep_deg'   angular separation between the two foci (degrees)
%
%   Other name-value parameters mirror focus_angle_sweep:
%     'N'             : 9
%     'd_ideal'       : 0.04880
%     'Max_iter'      : 40        (matches the 2-beam method's default)
%     'eps_dB'        : -20
%     'cone_rad'      : deg2rad(15)   smaller than v24's default so the two
%                                     cones don't merge for small sep
%     'fast_peaks'    : true
%     'angle_deg_list': 0:1:359
%     'save_movie'    : true
%     'filename'      : ''        auto: focus_sweep_2beam_sep<DEG>.<ext>
%     'frame_rate'    : 30
%     'clip_dB'       : -40
%     'show_progress' : true
%     'verbose'       : false
%
%   Outputs in res:
%     angles_deg_1, angles_deg_2, sep_deg, phi_mesh,
%     F_all (Nangles x M magnitude pattern), A_eff_all (Nangles x N),
%     times, movie_file.
%
%   Dependencies: perturb_method_2_beam_v5, d1d2Convert, findpeaks_fast.

    p = inputParser; p.FunctionName = 'focus_angle_sweep_2beam';
    addParameter(p,'sep_deg',         60,            @isnumeric);
    addParameter(p,'N',               9,             @(v) mod(v,2)==1 && v>=3);
    addParameter(p,'d_ideal',         0.04880,       @isnumeric);
    addParameter(p,'Max_iter',        40,            @isnumeric);
    addParameter(p,'eps_dB',          -20,           @isnumeric);
    addParameter(p,'cone_rad',        deg2rad(15),   @isnumeric);
    addParameter(p,'fast_peaks',      true,          @islogical);
    addParameter(p,'angle_deg_list',  0:1:359,       @isnumeric);
    addParameter(p,'save_movie',      true,          @islogical);
    addParameter(p,'filename',        '',            @(s) ischar(s) || isstring(s));
    addParameter(p,'frame_rate',      30,            @isnumeric);
    addParameter(p,'clip_dB',         -40,           @isnumeric);
    addParameter(p,'show_progress',   true,          @islogical);
    addParameter(p,'verbose',         false,         @islogical);
    parse(p, varargin{:}); a = p.Results;

    [x0, y0] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    x = x0(:); y = y0(:);

    angles_deg_1 = a.angle_deg_list(:);
    angles_rad_1 = deg2rad(angles_deg_1);
    sep_rad      = deg2rad(a.sep_deg);
    angles_rad_2 = mod(angles_rad_1 + sep_rad, 2*pi);
    angles_deg_2 = rad2deg(angles_rad_2);
    nA = numel(angles_rad_1);

    Mphi = 1000;
    phi_mesh = linspace(0, 2*pi, Mphi+1); phi_mesh(end) = [];

    F_all     = zeros(nA, Mphi);
    A_eff_all = zeros(nA, a.N);
    times     = zeros(nA, 1);

    fprintf('focus_angle_sweep_2beam: sep=%g deg, %d angles, fast_peaks=%d\n', ...
        a.sep_deg, nA, a.fast_peaks);
    t_total = tic;

    for k = 1:nA
        tic_k = tic;
        r = perturb_method_2_beam_v5(x, y, angles_rad_1(k), angles_rad_2(k), ...
            'Max_iter',        a.Max_iter, ...
            'eps_dB',          a.eps_dB, ...
            'cone_rad',        a.cone_rad, ...
            'fast_peaks',      a.fast_peaks, ...
            'verbose',         a.verbose, ...
            'show_plots',      false, ...
            'show_final_plot', false, ...
            'return_funcs',    false);
        times(k)       = toc(tic_k);
        F_all(k,:)     = r.final_function;     % already magnitude
        A_eff_all(k,:) = r.A_eff(:).';

        if a.show_progress && (mod(k,30)==0 || k==nA)
            fprintf('  %3d/%3d  phi_1=%3d  phi_2=%3d  t=%.3fs   total=%.1fs\n', ...
                k, nA, angles_deg_1(k), round(angles_deg_2(k)), times(k), toc(t_total));
        end
    end

    fprintf('Sweep complete in %.1f s.  Mean per-angle = %.3f s.\n', ...
        toc(t_total), mean(times));

    res.angles_deg_1 = angles_deg_1;
    res.angles_deg_2 = angles_deg_2;
    res.sep_deg      = a.sep_deg;
    res.phi_mesh     = phi_mesh;
    res.F_all        = F_all;
    res.A_eff_all    = A_eff_all;
    res.times        = times;
    res.movie_file   = '';
    res.params       = a;

    if ~a.save_movie, return; end

    if isempty(a.filename) || strlength(string(a.filename)) == 0
        if ispc || ismac
            ext = '.mp4'; profile = 'MPEG-4';
        else
            ext = '.avi'; profile = 'Motion JPEG AVI';
        end
        filename = sprintf('focus_sweep_2beam_sep%03d%s', round(a.sep_deg), ext);
    else
        filename = char(a.filename);
        [~,~,e] = fileparts(filename);
        switch lower(e)
            case '.mp4', profile = 'MPEG-4';
            case '.avi', profile = 'Motion JPEG AVI';
            otherwise,   profile = 'Motion JPEG AVI';
        end
    end

    fprintf('Writing movie: %s  (%d frames @ %.0f fps, profile=%s)\n', ...
        filename, nA, a.frame_rate, profile);

    [fig, pax] = build_movie_fig_2beam(a.sep_deg);
    v = VideoWriter(filename, profile);
    v.FrameRate = a.frame_rate;
    open(v);

    aborted = false; abort_msg = '';
    for k = 1:nA
        Fmag = F_all(k,:);
        F_dB = max(10*log10((Fmag.^2)/(max(Fmag)^2)), a.clip_dB);

        img = [];
        try
            draw_frame_2beam(pax, phi_mesh, F_dB, ...
                angles_rad_1(k), angles_rad_2(k), a.clip_dB, ...
                a.sep_deg, angles_deg_1(k), round(angles_deg_2(k)), times(k));
            img = print(fig, '-RGBImage', '-r0');
        catch ME1
            try, if isgraphics(fig), close(fig); end; catch, end
            [fig, pax] = build_movie_fig_2beam(a.sep_deg);
            try
                draw_frame_2beam(pax, phi_mesh, F_dB, ...
                    angles_rad_1(k), angles_rad_2(k), a.clip_dB, ...
                    a.sep_deg, angles_deg_1(k), round(angles_deg_2(k)), times(k));
                img = print(fig, '-RGBImage', '-r0');
            catch ME2
                aborted = true;
                abort_msg = sprintf('Frame %d failed twice (%s -> %s).', ...
                    k, ME1.identifier, ME2.identifier);
                break;
            end
        end

        try
            writeVideo(v, img);
        catch ME3
            aborted = true;
            abort_msg = sprintf('writeVideo failed at frame %d (%s).', k, ME3.identifier);
            break;
        end

        if a.show_progress && (mod(k, 60) == 0 || k == nA)
            fprintf('  frame %3d/%3d written\n', k, nA);
        end
    end

    try, close(v);            catch, end
    try, if isgraphics(fig), close(fig); end; catch, end

    if aborted
        warning('focus_angle_sweep_2beam:frame_fail', '%s Aborting movie write.', abort_msg);
        try, if exist(filename,'file'), delete(filename); end; catch, end
        return;
    end

    res.movie_file = fullfile(pwd, filename);
    fprintf('Saved movie to %s\n', res.movie_file);
end


function [fig, pax] = build_movie_fig_2beam(sep_deg)
    fig = figure('Name', sprintf('2-beam sweep: sep=%g°', sep_deg), ...
                 'Color','w', 'Position',[100 100 720 720], 'Visible','on');
    pax = polaraxes(fig);
    hold(pax, 'on');
end


function draw_frame_2beam(pax, phi_mesh, F_dB, phi1, phi2, clip_dB, sep_deg, deg1, deg2, t_sec)
    cla(pax);
    polarplot(pax, phi_mesh, F_dB,            'b-', 'LineWidth', 1.5);
    polarplot(pax, [phi1 phi1], [clip_dB 0],  'g-', 'LineWidth', 1.5);
    polarplot(pax, [phi2 phi2], [clip_dB 0],  'm-', 'LineWidth', 1.5);
    rlim(pax, [clip_dB 0]);
    title(pax, sprintf('2-beam   |   sep=%g°   |   \\phi_1=%3d°   \\phi_2=%3d°   |   t=%.3fs', ...
        sep_deg, deg1, deg2, t_sec));
    drawnow limitrate;
end
