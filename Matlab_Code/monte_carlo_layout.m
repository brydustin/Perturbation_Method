%% Monte Carlo study of random N-element drone layouts
%  For each trial:
%    - Draw N element positions uniformly in a disk of radius R_aperture,
%      rejecting configurations with any pair closer than d_min.
%    - Run perturb_method_v23 to form a beam at phi_0.
%    - Record: worst sidelobe (dB), best sidelobe (dB), gain @ phi_0 (dB).
%  Then compare against the ideal "1 center + regular (N-1)-gon" layout.
%
%  Dependencies: perturb_method_v23.m, d1d2Convert.m, directivity_met_v2.m,
%                plot_pattern_v5.m, findpeaks_circular.m.
%
%  Outputs:
%    mc_results struct with all recorded metrics
%    Figures: histograms of the 3 metrics + reference lines for ideal.

function mc_results = monte_carlo_layout(varargin)

    %% ---- Parameters (override via name-value pairs) ----
    p = inputParser;
    addParameter(p, 'N',           9,       @(v)isnumeric(v) && mod(v,2)==1 && v>=3);
    addParameter(p, 'N_trials',    500,     @isnumeric);
    addParameter(p, 'phi_0',       0,       @isnumeric);
    addParameter(p, 'Max_iter',    60,      @isnumeric);
    addParameter(p, 'eps_dB',      -20,     @isnumeric);
    addParameter(p, 'R_aperture',  0.15,    @isnumeric);   % disk radius for random draws (m); 1.5*lambda by default
    addParameter(p, 'd_min',       0.1,     @isnumeric);   % minimum pairwise separation (m); 1*lambda by default
    addParameter(p, 'd_ideal',     0.04880, @isnumeric);   % d1=d2 for reference octagon
    addParameter(p, 'rng_seed',    42,      @isnumeric);
    addParameter(p, 'verbose',     false,   @islogical);
    addParameter(p, 'show_ideal_pattern', false, @islogical);
    parse(p, varargin{:});
    a = p.Results;

    freq   = 3e9;
    lambda = 3e8 / freq;
    fprintf('lambda = %.4f m. R_aperture = %.4f m (%.2f lambda). d_min = %.4f m (%.2f lambda).\n', ...
            lambda, a.R_aperture, a.R_aperture/lambda, a.d_min, a.d_min/lambda);

    rng(a.rng_seed);

    %% ---- Pre-allocate storage ----
    worst_sl = nan(a.N_trials,1);
    best_sl  = nan(a.N_trials,1);
    gain_f0  = nan(a.N_trials,1);
    reject_count = 0;

    %% ---- Reference (ideal) layout ----
    [x_ref, y_ref] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    ref = run_one(x_ref, y_ref, a);
    fprintf('Ideal (1+%d-gon): worst=%.2f dB, best=%.2f dB, gain=%.2f dB\n', ...
            a.N-1, ref.worst, ref.best, ref.gain);

    %% ---- Monte Carlo loop ----
    t = 1;
    while t <= a.N_trials
        [xr, yr, ok] = draw_layout(a.N, a.R_aperture, a.d_min);
        if ~ok
            reject_count = reject_count + 1;
            if reject_count > 50 * a.N_trials
                error('Cannot satisfy d_min=%.4f in R=%.4f disk. Loosen constraints.', ...
                      a.d_min, a.R_aperture);
            end
            continue;
        end
        r = run_one(xr, yr, a);
        worst_sl(t) = r.worst;
        best_sl(t)  = r.best;
        gain_f0(t)  = r.gain;
        if a.verbose && mod(t,50)==0
            fprintf('  trial %d/%d: worst=%.2f best=%.2f gain=%.2f\n', ...
                    t, a.N_trials, r.worst, r.best, r.gain);
        end
        t = t + 1;
    end
    fprintf('Completed %d trials (%d rejected draws during search).\n', a.N_trials, reject_count);

    %% ---- Assemble output ----
    mc_results.worst_sl    = worst_sl;
    mc_results.best_sl     = best_sl;
    mc_results.gain_f0     = gain_f0;
    mc_results.ref         = ref;
    mc_results.params      = a;
    mc_results.lambda      = lambda;

    %% ---- Plots ----
    figure('Name','Monte Carlo: worst sidelobe (dB)');
    histogram(worst_sl, 40); hold on;
    xline(ref.worst, 'r', 'LineWidth', 2, 'Label', 'ideal (n-1)-gon');
    xlabel('Worst (highest) sidelobe [dB]'); ylabel('count');
    title(sprintf('Worst sidelobe over %d random layouts', a.N_trials));

    figure('Name','Monte Carlo: best sidelobe (dB)');
    histogram(best_sl, 40); hold on;
    xline(ref.best, 'r', 'LineWidth', 2, 'Label', 'ideal (n-1)-gon');
    xlabel('Best (deepest) sidelobe [dB]'); ylabel('count');
    title(sprintf('Best sidelobe over %d random layouts', a.N_trials));

    figure('Name','Monte Carlo: gain in focus direction');
    histogram(gain_f0, 40); hold on;
    xline(ref.gain, 'r', 'LineWidth', 2, 'Label', 'ideal (n-1)-gon');
    xlabel('Gain @ \phi_0 [dB]'); ylabel('count');
    title(sprintf('Focus-direction gain over %d random layouts', a.N_trials));
end


%% ---- Draw one candidate layout (rejection sampling) ----
function [x, y, ok] = draw_layout(N, R, d_min)
    max_attempts = 2000;
    x = zeros(N,1); y = zeros(N,1);
    for i = 1:N
        for attempt = 1:max_attempts
            rho   = R * sqrt(rand());
            theta = 2*pi*rand();
            xc = rho*cos(theta); yc = rho*sin(theta);
            if i == 1
                x(i) = xc; y(i) = yc; break;
            end
            d2 = (x(1:i-1)-xc).^2 + (y(1:i-1)-yc).^2;
            if all(d2 >= d_min^2)
                x(i) = xc; y(i) = yc; break;
            end
            if attempt == max_attempts
                ok = false; return;
            end
        end
    end
    ok = true;
end


%% ---- Run perturb_method_v23 on one layout and extract metrics ----
function r = run_one(x, y, a)
    res = perturb_method_v23( ...
        a.Max_iter, a.eps_dB, x(:), y(:), a.phi_0, ...
        'verbose', false, 'show_plots', false, ...
        'show_final_plot', false, 'return_funcs', false, ...
        'full_loop', false);
    % worst = highest (least negative) sidelobe in final pattern
    % best  = deepest (most negative) sidelobe in final pattern
    Slobe = res.phi_s_sorted_fin;   %#ok<NASGU>  % angles (for reference)
    % res.phi_s_sorted_fin is angles; values are in res (we re-extract below)
    % Recompute sidelobe levels from final pattern to be robust:
    phi_mesh = linspace(0, 2*pi, 1001); phi_mesh(end) = [];
    F = res.final_function;
    Fmag = abs(F);
    [pv, pl] = findpeaks_circular(Fmag, phi_mesh);
    if isempty(pv)
        r.worst = NaN; r.best = NaN;
    else
        % remove main beam (closest peak to phi_0)
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
