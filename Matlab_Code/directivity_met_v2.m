%% Directivity Metric Calculator (Circular-Aware)
% Version 2: Uses findpeaks_circular to correctly handle wrap-around
% 11/26/2025

%% Helper Functions
function bw = directivity_met_v2(phi, F_total, phi_0)

function d = angleDiffCircular(a, b)
    % Circular difference a - b wrapped to [-pi, pi)
    d = angle(exp(1j*(a - b)));
end

function ang_05 = halfPowerSearch(Fnorm, phi, startIdx, direction, halfpower)
% direction = +1 (right) or -1 (left)

    N = numel(Fnorm);
    i = startIdx;

    % Move until magnitude drops below half-power
    while true
        next = i + direction;
        if next < 1
            next = N;        % wrap left → end
        elseif next > N
            next = 1;        % wrap right → start
        end

        % Stop if we've looped full circle (no crossing)
        if next == startIdx
            ang_05 = NaN;
            return;
        end

        if Fnorm(next) < halfpower
            % Interpolate between i and next
            Fseg = [Fnorm(i), Fnorm(next)];
            phis = [phi(i), phi(next)];
            % fix wrap (ensure strictly increasing for interp1)
            if direction == +1 && phis(2) < phis(1)
                phis(2) = phis(2) + 2*pi;
            elseif direction == -1 && phis(2) > phis(1)
                phis(2) = phis(2) - 2*pi;
            end

            ang_05 = interp1(Fseg, phis, halfpower);

            % wrap to [0,2pi)
            ang_05 = mod(ang_05, 2*pi);
            return;
        end

        i = next;
    end
end

%%
    % Ensure column vectors
    phi = phi(:);
    F_total = F_total(:);

    %% ----- Convert to linear magnitude -----
    Fmag = abs(F_total);

    %% ----- Normalize (peak = 1) -----
    [Fpeak, idx_peak] = max(Fmag);
    Fnorm = Fmag / Fpeak;

    %% ============================================================
    %%  Use CIRCULAR peak finder (fixes 0↔2π seam problem)
    %% ============================================================
    [peakVals, peakLocs] = findpeaks_circular(Fnorm.', phi.');

    if isempty(peakVals)
        error('directivity_met_v2: No peaks found.');
    end

    %% ----- Identify main beam: closest peak to phi_0 on circular domain -----
    angDiff = angleDiffCircular(peakLocs, phi_0);  % circular distance in radians
    [~, idx_main] = min(abs(angDiff));

    main_peak_angle = peakLocs(idx_main);
    main_peak_value = peakVals(idx_main);

    %% ----- Find index of the peak in original phi grid -----
    [~, mIdx] = min(abs(angleDiffCircular(phi, main_peak_angle)));

    %% ----- Half-power threshold (linear) -----
    %halfpower = 0.5; %original
    halfpower = 1/sqrt(2);

    %% ============================================================
    %%  RIGHT half-power crossing — circular search
    %% ============================================================
    right_05 = halfPowerSearch(Fnorm, phi, mIdx, +1, halfpower);

    %% ============================================================
    %%  LEFT half-power crossing — circular search
    %% ============================================================
    left_05  = halfPowerSearch(Fnorm, phi, mIdx, -1, halfpower);

    %% ----- Compute beamwidth -----
    if isnan(left_05) || isnan(right_05)
        bw_val = NaN;
    else
        bw_val = angleDiffCircular(right_05, left_05);  % circular width
    end

    %% ----- Output struct -----
    bw.main_peak_angle = main_peak_angle;
    bw.peak_value      = main_peak_value * Fpeak;  % restore original scale
    bw.left_05         = left_05;
    bw.right_05        = right_05;
    bw.beamwidth       = bw_val;
end
