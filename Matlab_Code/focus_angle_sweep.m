function res = focus_angle_sweep(varargin)
%FOCUS_ANGLE_SWEEP  Sweep the focus direction phi_0 in 1-degree steps from
%   0 to 359, run the selected beamforming method at each angle (full
%   convergence), and assemble an animated polar-pattern movie. Each frame
%   shows only the FINAL pattern produced for that angle.
%
%   Defaults: method='v24', save the movie in the current working directory.
%
%   Name-value parameters
%   ---------------------
%     'method'           : 'v24' (default) | 'constrained'
%     'N'                : 9                array element count
%     'd_ideal'          : 0.04880          ring spacing
%     'Max_iter'         : 200              method iteration budget
%     'eps_dB'           : -20              method sidelobe target
%     'cone_rad'         : deg2rad(30)
%     'max_outer_passes' : 3                (constrained only)
%     'fast_peaks'       : true             use findpeaks_fast in the method
%     'angle_deg_list'   : 0:1:359          sweep set in degrees
%     'save_movie'       : true             write file to pwd by default
%     'filename'         : ''               auto: focus_sweep_<method>.<ext>
%                                            ext: .avi on Linux, .mp4 on Win/Mac
%     'frame_rate'       : 30               movie fps
%     'clip_dB'          : -40              dB floor for normalized polar plot
%     'show_progress'    : true             print progress every 30 angles
%     'verbose'          : false            also print method's per-call info
%
%   Outputs
%   -------
%     res.angles_deg   sweep set (Nx1)
%     res.angles_rad   sweep set in radians (Nx1)
%     res.phi_mesh     1xM dense angle mesh used in the patterns
%     res.F_all        N x M complex pattern matrix (final pattern per angle)
%     res.A_eff_all    N x Nelem complex coefficients per angle
%     res.times        N x 1 per-angle method runtime
%     res.movie_file   full path of saved movie (empty if not saved)
%     res.method       'v24' or 'constrained'
%
%   Dependencies
%   ------------
%     perturb_method_v24, perturb_method_constrained_v2, d1d2Convert,
%     findpeaks_fast (used inside the methods)

    p = inputParser; p.FunctionName = 'focus_angle_sweep';
    addParameter(p,'method',           'v24',         @(s) ischar(s) || isstring(s));
    addParameter(p,'N',                9,             @(v) mod(v,2)==1 && v>=3);
    addParameter(p,'d_ideal',          0.04880,       @isnumeric);
    addParameter(p,'Max_iter',         200,           @isnumeric);
    addParameter(p,'eps_dB',           -20,           @isnumeric);
    addParameter(p,'cone_rad',         deg2rad(30),   @isnumeric);
    addParameter(p,'max_outer_passes', 3,             @isnumeric);
    addParameter(p,'fast_peaks',       true,          @islogical);
    addParameter(p,'angle_deg_list',   0:1:359,       @isnumeric);
    addParameter(p,'save_movie',       true,          @islogical);
    addParameter(p,'filename',         '',            @(s) ischar(s) || isstring(s));
    addParameter(p,'frame_rate',       30,            @isnumeric);
    addParameter(p,'clip_dB',          -40,           @isnumeric);
    addParameter(p,'show_progress',    true,          @islogical);
    addParameter(p,'verbose',          false,         @islogical);
    parse(p, varargin{:}); a = p.Results;

    method_str = lower(string(a.method));
    if ~ismember(method_str, ["v24","constrained"])
        error('focus_angle_sweep: method must be "v24" or "constrained" (got "%s").', a.method);
    end

    [x0, y0] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    x = x0(:); y = y0(:);

    angles_deg = a.angle_deg_list(:);
    angles_rad = deg2rad(angles_deg);
    nA = numel(angles_rad);

    Mphi = 1000;
    phi_mesh = linspace(0, 2*pi, Mphi+1); phi_mesh(end) = [];

    F_all     = zeros(nA, Mphi);
    A_eff_all = zeros(nA, a.N);
    times     = zeros(nA, 1);

    fprintf('focus_angle_sweep: method=%s, %d angles, fast_peaks=%d\n', ...
        char(method_str), nA, a.fast_peaks);
    t_total = tic;

    for k = 1:nA
        phi0 = angles_rad(k);
        tic_k = tic;
        switch method_str
            case "v24"
                r = perturb_method_v24(a.Max_iter, a.eps_dB, x, y, phi0, ...
                    'cone_rad',        a.cone_rad, ...
                    'fast_peaks',      a.fast_peaks, ...
                    'verbose',         a.verbose, ...
                    'show_plots',      false, ...
                    'show_final_plot', false, ...
                    'return_funcs',    false);
            case "constrained"
                r = perturb_method_constrained_v2(a.Max_iter, a.eps_dB, x, y, phi0, ...
                    'cone_rad',         a.cone_rad, ...
                    'max_outer_passes', a.max_outer_passes, ...
                    'fast_peaks',       a.fast_peaks, ...
                    'verbose',          a.verbose, ...
                    'show_final_plot',  false, ...
                    'return_funcs',     false);
        end
        times(k)       = toc(tic_k);
        F_all(k,:)     = r.final_function;
        A_eff_all(k,:) = r.A_eff(:).';

        if a.show_progress && (mod(k,30)==0 || k==nA)
            fprintf('  %3d/%3d  phi_0=%3d deg   t=%.3fs   total=%.1fs\n', ...
                k, nA, angles_deg(k), times(k), toc(t_total));
        end
    end

    fprintf('Sweep complete in %.1f s.  Mean per-angle = %.3f s.\n', ...
        toc(t_total), mean(times));

    res.angles_deg = angles_deg;
    res.angles_rad = angles_rad;
    res.phi_mesh   = phi_mesh;
    res.F_all      = F_all;
    res.A_eff_all  = A_eff_all;
    res.times      = times;
    res.method     = char(method_str);
    res.movie_file = '';
    res.params     = a;

    if ~a.save_movie
        return;
    end

    % ---- Choose container & profile by platform (unless caller overrides) ----
    if isempty(a.filename) || strlength(string(a.filename)) == 0
        if ispc || ismac
            ext = '.mp4'; profile = 'MPEG-4';
        else
            ext = '.avi'; profile = 'Motion JPEG AVI';
        end
        filename = sprintf('focus_sweep_%s%s', char(method_str), ext);
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

    [fig, pax] = build_movie_fig(char(method_str));
    v = VideoWriter(filename, profile);
    v.FrameRate = a.frame_rate;
    open(v);

    aborted = false;
    abort_msg = '';
    for k = 1:nA
        Fmag = abs(F_all(k,:));
        F_dB = max(10*log10((Fmag.^2)/(max(Fmag)^2)), a.clip_dB);

        img = [];
        try
            draw_frame(pax, phi_mesh, F_dB, angles_rad(k), a.clip_dB, ...
                       char(method_str), angles_deg(k), times(k));
            img = print(fig, '-RGBImage', '-r0');
        catch ME1
            % Canvas got out of sync; rebuild the figure once and retry.
            try, if isgraphics(fig), close(fig); end; catch, end
            [fig, pax] = build_movie_fig(char(method_str));
            try
                draw_frame(pax, phi_mesh, F_dB, angles_rad(k), a.clip_dB, ...
                           char(method_str), angles_deg(k), times(k));
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

    % Always close the writer and figure
    try, close(v);            catch, end
    try, if isgraphics(fig), close(fig); end; catch, end

    if aborted
        warning('focus_angle_sweep:frame_fail', '%s Aborting movie write.', abort_msg);
        % Try to delete the partial file so we don't leave a corrupt artifact
        try, if exist(filename,'file'), delete(filename); end; catch, end
        res.movie_file = '';
        return;
    end

    res.movie_file = fullfile(pwd, filename);
    fprintf('Saved movie to %s\n', res.movie_file);
end


function [fig, pax] = build_movie_fig(method_str)
    fig = figure('Name', sprintf('Focus sweep: %s', method_str), ...
                 'Color','w', 'Position',[100 100 720 720], ...
                 'Visible','on');
    pax = polaraxes(fig);
    hold(pax,'on');
end


function draw_frame(pax, phi_mesh, F_dB, phi0, clip_dB, method_str, ang_deg, t_sec)
    cla(pax);
    polarplot(pax, phi_mesh, F_dB,            'b-', 'LineWidth', 1.5);
    polarplot(pax, [phi0 phi0], [clip_dB 0],  'g-', 'LineWidth', 1.5);
    rlim(pax, [clip_dB 0]);
    title(pax, sprintf('%s   |   focus \\phi_0 = %3d°   |   t = %.3f s', ...
        method_str, ang_deg, t_sec));
    drawnow limitrate;
end
