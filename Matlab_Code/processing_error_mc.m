%% Processing-error Monte Carlo
%  1. Run perturb_method_v23 once on the ideal (1+octagon) layout to obtain
%     the optimized complex currents A_eff.
%  2. For each of N_trials, add independent complex noise n_i = r_i * exp(j*theta_i)
%     to each of the N currents, where
%         r_i     ~ Uniform(0, noise_max_mod)   (default 1)
%         theta_i ~ Uniform(0, 2*pi)
%     so each n_i lies in the complex disk of radius noise_max_mod with a
%     density proportional to 1/|n_i|. (This matches the literal reading of
%     "modulus chosen uniformly on [0, 1]".)
%  3. Recompute the pattern with the noisy currents and record
%     worst sidelobe, best (deepest) sidelobe, and gain @ phi_0.
%
%  Dependencies: perturb_method_v23.m, d1d2Convert.m, findpeaks_circular.m.

function res = processing_error_mc(varargin)

    p = inputParser;
    addParameter(p, 'N',             9,       @(v) mod(v,2)==1 && v>=3);
    addParameter(p, 'd_ideal',       0.04880, @isnumeric);
    addParameter(p, 'phi_0',         0,       @isnumeric);
    addParameter(p, 'Max_iter',      60,      @isnumeric);
    addParameter(p, 'eps_dB',        -20,     @isnumeric);
    addParameter(p, 'N_trials',      500,     @isnumeric);
    addParameter(p, 'noise_max_mod', 1.0,     @isnumeric);
    addParameter(p, 'rng_seed',      42,      @isnumeric);
    addParameter(p, 'verbose',       false,   @islogical);
    parse(p, varargin{:});
    a = p.Results;

    rng(a.rng_seed);
    freq = 3e9; lambda = 3e8/freq; k0 = 2*pi/lambda;

    [x, y] = d1d2Convert(a.d_ideal, a.d_ideal, a.N);
    x = x(:); y = y(:);

    opt = perturb_method_v23(a.Max_iter, a.eps_dB, x, y, a.phi_0, ...
                             'verbose', false, 'show_plots', false, ...
                             'show_final_plot', false, 'return_funcs', false, ...
                             'full_loop', false);
    A_eff = opt.A_eff(:);
    N = numel(A_eff);

    phi = linspace(0, 2*pi, 1001); phi(end) = [];
    phase_mat = exp(1j * k0 * (x * cos(phi) + y * sin(phi)));   % N x M

    % Noiseless reference
    [ref.worst, ref.best, ref.gain] = pattern_metrics(A_eff, phase_mat, phi, a.phi_0);
    fprintf('Reference (noiseless): worst=%.2f dB, best=%.2f dB, gain=%.2f dB\n', ...
            ref.worst, ref.best, ref.gain);

    worst = nan(a.N_trials, 1);
    best  = nan(a.N_trials, 1);
    gain  = nan(a.N_trials, 1);

    for t = 1:a.N_trials
        r_mod = a.noise_max_mod * rand(N, 1);
        r_ph  = 2*pi * rand(N, 1);
        noise = r_mod .* exp(1j * r_ph);
        A_noisy = A_eff + noise;

        [worst(t), best(t), gain(t)] = pattern_metrics(A_noisy, phase_mat, phi, a.phi_0);

        if a.verbose && mod(t, 50) == 0
            fprintf('  trial %d/%d: worst=%.2f best=%.2f gain=%.2f\n', ...
                    t, a.N_trials, worst(t), best(t), gain(t));
        end
    end

    res.worst    = worst;
    res.best     = best;
    res.gain     = gain;
    res.ref      = ref;
    res.A_eff    = A_eff;
    res.lambda   = lambda;
    res.params   = a;

    figure('Name','Processing error: worst sidelobe');
    histogram(worst, 40); hold on;
    xline(ref.worst, 'r', 'LineWidth', 2, 'Label', 'noiseless');
    xlabel('Worst sidelobe [dB]'); ylabel('count');
    title(sprintf('Worst sidelobe over %d noise realizations', a.N_trials));

    figure('Name','Processing error: best sidelobe');
    histogram(best, 40); hold on;
    xline(ref.best, 'r', 'LineWidth', 2, 'Label', 'noiseless');
    xlabel('Best (deepest) sidelobe [dB]'); ylabel('count');
    title(sprintf('Best sidelobe over %d noise realizations', a.N_trials));

    figure('Name','Processing error: gain');
    histogram(gain, 40); hold on;
    xline(ref.gain, 'r', 'LineWidth', 2, 'Label', 'noiseless');
    xlabel('Gain @ \phi_0 [dB]'); ylabel('count');
    title(sprintf('Focus-direction gain over %d noise realizations', a.N_trials));
end


function [worst, best, gain] = pattern_metrics(A, phase_mat, phi, phi_0)
    F = A.' * phase_mat;
    Fmag = abs(F);
    [pv, pl] = findpeaks_circular(Fmag, phi);
    if isempty(pv)
        worst = NaN; best = NaN;
    else
        dphi = abs(atan2(sin(pl - phi_0), cos(pl - phi_0)));
        [~, im] = min(dphi);
        pv(im) = [];
        if isempty(pv)
            worst = NaN; best = NaN;
        else
            sl_dB = 10*log10((pv.^2) / (max(Fmag).^2));
            worst = max(sl_dB);
            best  = min(sl_dB);
        end
    end
    I = trapz(phi, Fmag.^2);
    F0 = interp1(phi, F, phi_0, 'linear', 'extrap');
    gain = 10*log10((abs(F0).^2 * 4*pi) / I);
end
