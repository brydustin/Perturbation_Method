%% Systematic 2D (dx, dy) perturbation of a single element from the ideal (n-1)-gon
%  Keep element 1 at the origin and 7 of the 8 outer elements fixed on the
%  regular octagon (radius d_ideal). For the chosen outer element moved_idx,
%  sweep its position over a cartesian grid:
%       (x, y) = (x0 + dx, y0 + dy),
%  where (x0, y0) is the element's ideal position. (dx, dy) = (0, 0) is the
%  unperturbed (ideal) configuration.
%
%  For each (dx, dy), run perturb_method_v23 and record:
%       - worst sidelobe (dB)
%       - best (deepest) sidelobe (dB)
%       - gain at phi_0 (dB)
%
%  Produces three 3D surface plots, one per metric, over the (dx, dy) grid.
%
%  Dependencies: perturb_method_v23.m, d1d2Convert.m, directivity_met_v2.m,
%                plot_pattern_v5.m, findpeaks_circular.m.

function sweep = systematic_perturbation(varargin)

    p = inputParser;
    addParameter(p, 'N',         9,       @(v) mod(v,2)==1 && v>=3);
    addParameter(p, 'd_ideal',   0.04880, @isnumeric);
    addParameter(p, 'phi_0',     0,       @isnumeric);
    addParameter(p, 'Max_iter',  60,      @isnumeric);
    addParameter(p, 'eps_dB',    -20,     @isnumeric);
    addParameter(p, 'moved_idx', 2,       @(v) isnumeric(v) && v >= 2);
    % 2D sweep grid: absolute offsets from the element's ideal (x0, y0)
    addParameter(p, 'dx_list',   linspace(-0.03, 0.03, 21), @isnumeric);
    addParameter(p, 'dy_list',   linspace(-0.03, 0.03, 21), @isnumeric);
    addParameter(p, 'verbose',   false,   @islogical);
    parse(p, varargin{:});
    a = p.Results;

    freq   = 3e9;
    lambda = 3e8 / freq;

    % Ideal geometry
    [x0, y0] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    if a.moved_idx < 2 || a.moved_idx > a.N
        error('moved_idx must be an outer-element index in [2, N].');
    end
    x0_k = x0(a.moved_idx);
    y0_k = y0(a.moved_idx);

    dx_list = a.dx_list(:).';   % row
    dy_list = a.dy_list(:).';
    Nx = numel(dx_list);
    Ny = numel(dy_list);

    [DX, DY] = meshgrid(dx_list, dy_list);   % Ny x Nx
    worst_sl = nan(Ny, Nx);
    best_sl  = nan(Ny, Nx);
    gain_f0  = nan(Ny, Nx);

    total = Nx * Ny;
    done  = 0;
    for iy = 1:Ny
        for ix = 1:Nx
            x = x0; y = y0;
            x(a.moved_idx) = x0_k + dx_list(ix);
            y(a.moved_idx) = y0_k + dy_list(iy);

            r = run_one(x, y, a);
            worst_sl(iy, ix) = r.worst;
            best_sl(iy, ix)  = r.best;
            gain_f0(iy, ix)  = r.gain;

            done = done + 1;
            if a.verbose && mod(done, max(1, round(total/20))) == 0
                fprintf('  sweep %d/%d (dx=%.4f, dy=%.4f): worst=%.2f best=%.2f gain=%.2f\n', ...
                        done, total, dx_list(ix), dy_list(iy), r.worst, r.best, r.gain);
            end
        end
    end

    sweep.dx_list  = dx_list;
    sweep.dy_list  = dy_list;
    sweep.DX       = DX;
    sweep.DY       = DY;
    sweep.worst_sl = worst_sl;
    sweep.best_sl  = best_sl;
    sweep.gain_f0  = gain_f0;
    sweep.lambda   = lambda;
    sweep.ideal_xy = [x0_k, y0_k];
    sweep.params   = a;

    %% ---- 3D surface plots ----
    plot_surface(DX, DY, worst_sl, a.moved_idx, ...
        'Worst sidelobe [dB]', 'Worst sidelobe over (dx, dy) perturbation');
    plot_surface(DX, DY, best_sl, a.moved_idx, ...
        'Best (deepest) sidelobe [dB]', 'Best sidelobe over (dx, dy) perturbation');
    plot_surface(DX, DY, gain_f0, a.moved_idx, ...
        'Gain @ \phi_0 [dB]', 'Focus gain over (dx, dy) perturbation');
end


function plot_surface(DX, DY, Z, moved_idx, zlabel_str, ttl)
    figure('Name', ttl);
    surf(DX, DY, Z, 'EdgeColor', 'none');
    hold on;
    % Mark the ideal (dx, dy) = (0, 0) point on the surface
    z0 = interp2(DX, DY, Z, 0, 0, 'linear');
    if ~isnan(z0)
        plot3(0, 0, z0, 'ro', 'MarkerFaceColor', 'r', 'MarkerSize', 8);
    end
    xlabel('\deltax [m]'); ylabel('\deltay [m]'); zlabel(zlabel_str);
    title(sprintf('%s (element %d perturbed)', ttl, moved_idx));
    colorbar; view(40, 30); grid on;
end


function r = run_one(x, y, a)
    res = perturb_method_v23( ...
        a.Max_iter, a.eps_dB, x(:), y(:), a.phi_0, ...
        'verbose', false, 'show_plots', false, ...
        'show_final_plot', false, 'return_funcs', false, ...
        'full_loop', false);

    phi_mesh = linspace(0, 2*pi, 1001); phi_mesh(end) = [];
    F = res.final_function;
    Fmag = abs(F);
    [pv, pl] = findpeaks_circular(Fmag, phi_mesh);
    if isempty(pv)
        r.worst = NaN; r.best = NaN;
    else
        dphi = abs(atan2(sin(pl - a.phi_0), cos(pl - a.phi_0)));
        [~, im] = min(dphi);
        pv(im) = [];
        if isempty(pv)
            r.worst = NaN; r.best = NaN;
        else
            sl_dB = 10*log10((pv.^2) / (max(Fmag).^2));
            r.worst = max(sl_dB);
            r.best  = min(sl_dB);
        end
    end
    r.gain = res.final_gain2D;
end
