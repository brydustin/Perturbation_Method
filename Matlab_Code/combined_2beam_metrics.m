function metrics = combined_2beam_metrics(resA, resB, phi_0_1, phi_0_2, x, y, varargin)
% COMBINED_2BEAM_METRICS
%   Mosier-style coefficient-summed combination of two 1-beam solver
%   results, followed by the full metric set: 2D and 3D gain at both
%   foci, main-beam skews (signed and absolute, rad and deg), half-power
%   beamwidth at both foci, and the final max sidelobe.
%
%   Variant-agnostic on purpose. Works for any 2-beam superposition:
%     - 1-B-1-N (perturb_method_v25 with null at partner)
%     - 1-B no-null (perturb_method_v25 with 'null_phi', [])
%     - Projection-started (perturb_method_v25 with 'A_init', I_proj)
%     - Cramer Simultaneous Constraints (Crammer_Simultaneous_Constraints)
%   as long as resA and resB each carry .A_eff and .final_function with
%   the conventions used by every solver in the codebase.
%
% Required inputs
%   resA, resB   - structs from any compatible 1-beam solver with fields
%                    .A_eff           (Nx1 complex coefficient vector)
%                    .final_function  (1xM pattern on the standard phi mesh)
%   phi_0_1      - primary focus direction (rad)
%   phi_0_2      - secondary focus direction (rad)
%   x, y         - Nx1 element coordinate vectors (m)
%
% Optional name-value parameters (defaults shown)
%   'z'          ([])           Nx1 z-coordinates; empty -> all zeros
%   'theta_0'    (pi/2)         elevation at which gain is evaluated (rad)
%   'cone_rad'   ([])           if nonempty, drop peaks within this angle
%                               of EITHER focus from sidelobe consideration
%                               (rad). [] matches perturb_method_2_beam_v5's
%                               post-loop "Additional Calculations" block,
%                               which doesn't apply a cone at the report stage.
%   'phi_mesh'   (standard)     azimuth mesh; must match the mesh used by
%                               the component solvers, or F_total addition
%                               is nonsensical
%   'theta_mesh' (standard)     elevation mesh
%   'k0'         (3 GHz)        wavenumber = 2*pi*freq/c
%
% Output - single struct:
%   .final_function, .A_total
%   .Big_phi_final_1, .Big_phi_final_2
%   .Big_Val_final_1, .Big_Val_final_2
%   .final_gain2D_1, .final_gain2D_2
%   .final_gain3D_1, .final_gain3D_2
%   .main_beam_angle_final_1, .main_beam_angle_final_2          (rad)
%   .main_beam_skew_final_1, .main_beam_skew_final_2            (rad, abs)
%   .main_beam_skew_final_1_deg, .main_beam_skew_final_2_deg    (deg, abs)
%   .main_beam_skew_final_1_signed, .main_beam_skew_final_2_signed         (rad)
%   .main_beam_skew_final_1_signed_deg, .main_beam_skew_final_2_signed_deg (deg)
%   .final_max_sidelobe_dB, .final_max_sidelobe_phi, .final_max_sidelobe_phi_deg
%   .beamwidth_1, .beamwidth_2                                  (rad)
%   .beamwidth_1_deg, .beamwidth_2_deg                          (deg)
%   .bw1_left_05, .bw1_right_05, .bw2_left_05, .bw2_right_05    (rad,
%       half-power edge angles in [0,2*pi), for plotting BW edges)
%
% Beamwidth convention: each beam's half-power (-3 dB) width is measured
%   relative to that beam's OWN peak value, not the global pattern max.
%   (directivity_met_v2 normalizes to the global max, which breaks for
%   the weaker of two beams; do not mix the two conventions.) The width
%   is the circular arc from the left -3 dB crossing to the right -3 dB
%   crossing through the beam peak. NaN if the pattern never drops below
%   the threshold (beams merged into one broad lobe).
%
% Gain convention: the field is evaluated EXACTLY at each focus from
%   A_total (no interpolation), so foci falling between mesh points --
%   including inside the last segment before 2*pi, where interp2's
%   0-fill used to return -Inf dB -- are handled correctly. Pattern
%   integrals use trapz on the open [0, 2*pi) mesh, matching every other
%   solver in the codebase so gains stay directly comparable.
%
% Example usage (1-B-1-N variant):
%   resA = perturb_method_v25(Max_iter, eps_dB, x, y, phi_0_1, ...
%       'null_phi', phi_0_2, 'show_plots', false, 'verbose', false);
%   resB = perturb_method_v25(Max_iter, eps_dB, x, y, phi_0_2, ...
%       'null_phi', phi_0_1, 'show_plots', false, 'verbose', false);
%   m = combined_2beam_metrics(resA, resB, phi_0_1, phi_0_2, x, y);

    % ---- Parse optional arguments ----
    M_default = 1000;
    phi_default   = linspace(0, 2*pi, M_default+1);
    phi_default(end) = [];
    theta_default = linspace(0, pi, M_default);
    k0_default    = 2*pi*3e9/3e8;

    p = inputParser;
    addParameter(p, 'z',          [],           @isnumeric);
    addParameter(p, 'theta_0',    pi/2,         @isnumeric);
    addParameter(p, 'cone_rad',   [],           @isnumeric);
    addParameter(p, 'phi_mesh',   phi_default,  @isnumeric);
    addParameter(p, 'theta_mesh', theta_default,@isnumeric);
    addParameter(p, 'k0',         k0_default,   @isnumeric);
    parse(p, varargin{:});
    a = p.Results;

    x = x(:);
    y = y(:);
    if isempty(a.z)
        z = zeros(size(x));
    else
        z = a.z(:);
    end
    N = numel(x);
    phi_mesh   = a.phi_mesh(:).';
    theta_mesh = a.theta_mesh(:);
    k0         = a.k0;
    theta_0    = a.theta_0;

    % ---- Mosier-style coefficient-summed combination ----
    % Scale each beam so its single-beam pattern peaks at N before summing,
    % AND apply the matching scale to its A_eff so the coefficient sum
    % stays self-consistent with the pattern sum. Re-evaluate via F2d
    % and rescale so peaks of F_total match peaks of the pattern sum.

    fA = resA.final_function(:).';
    fB = resB.final_function(:).';
    AA = resA.A_eff(:);
    AB = resB.A_eff(:);

    if numel(AA) ~= N || numel(AB) ~= N
        error('combined_2beam_metrics:sizeMismatch', ...
            'A_eff in component results must be length N = %d.', N);
    end
    if numel(fA) ~= numel(phi_mesh) || numel(fB) ~= numel(phi_mesh)
        error('combined_2beam_metrics:meshMismatch', ...
            ['Component final_function lengths (%d, %d) must match phi_mesh ' ...
             '(%d). Pass ''phi_mesh'' if your solver uses a different mesh.'], ...
            numel(fA), numel(fB), numel(phi_mesh));
    end

    maxA = max(abs(fA)); if maxA == 0, maxA = 1; end
    maxB = max(abs(fB)); if maxB == 0, maxB = 1; end

    F_sum_scaled = (N * fA / maxA) + (N * fB / maxB);
    A_total      = (N * AA / maxA) + (N * AB / maxB);

    % F_eval is the UNSCALED re-evaluated pattern; gains are computed from
    % it (and exact A_total evaluations) so the cosmetic rescale below
    % never enters any ratio.
    F_eval = local_F2d(phi_mesh, A_total, x, y, k0);
    den    = max(abs(F_eval));
    pattern_ok = (den >= 1e-14);
    if ~pattern_ok
        warning('combined_2beam_metrics:zeroPattern', ...
            'Re-evaluated pattern has near-zero magnitude; reporting raw sum.');
        F_total = F_sum_scaled;
    else
        F_total = F_eval * (max(abs(F_sum_scaled)) / den);
    end

    metrics.final_function = F_total;
    metrics.A_total        = A_total;

    % ---- Locate the two main beams (wrap-aware) ----
    Fmag = abs(F_total);
    [pV, pL] = local_findpeaks_circular(Fmag, phi_mesh);

    if isempty(pV)
        % Degenerate pattern: no peaks found at all. Fall back to focus angles.
        metrics.Big_phi_final_1 = phi_0_1;
        metrics.Big_Val_final_1 = local_interp_mag(phi_mesh, F_total, phi_0_1);
        metrics.Big_phi_final_2 = phi_0_2;
        metrics.Big_Val_final_2 = local_interp_mag(phi_mesh, F_total, phi_0_2);
    else
        % Wrap-aware "nearest peak to phi_0_1"
        d1 = abs(atan2(sin(pL - phi_0_1), cos(pL - phi_0_1)));
        [~, i1] = min(d1);
        metrics.Big_phi_final_1 = pL(i1);
        metrics.Big_Val_final_1 = pV(i1);
        pV(i1) = []; pL(i1) = [];

        if isempty(pV)
            % Only one peak total — both beams collapsed into one lobe.
            metrics.Big_phi_final_2 = phi_0_2;
            metrics.Big_Val_final_2 = local_interp_mag(phi_mesh, F_total, phi_0_2);
        else
            d2 = abs(atan2(sin(pL - phi_0_2), cos(pL - phi_0_2)));
            [~, i2] = min(d2);
            metrics.Big_phi_final_2 = pL(i2);
            metrics.Big_Val_final_2 = pV(i2);
            pV(i2) = []; pL(i2) = [];
        end
    end

    % ---- Optional cone filter on sidelobe candidates ----
    if ~isempty(a.cone_rad) && ~isempty(pL)
        d1c = abs(atan2(sin(pL - phi_0_1), cos(pL - phi_0_1)));
        d2c = abs(atan2(sin(pL - phi_0_2), cos(pL - phi_0_2)));
        keep = (d1c > a.cone_rad) & (d2c > a.cone_rad);
        pV = pV(keep);
        pL = pL(keep);
    end

    % ---- Final max sidelobe ----
    if isempty(pV)
        metrics.final_max_sidelobe_dB      = -Inf;
        metrics.final_max_sidelobe_phi     = NaN;
        metrics.final_max_sidelobe_phi_deg = NaN;
    else
        pV_dB = 10*log10((pV.^2) / max(Fmag).^2);
        [Slobe_sorted, ix] = sort(pV_dB, 'descend');
        metrics.final_max_sidelobe_dB      = Slobe_sorted(1);
        metrics.final_max_sidelobe_phi     = pL(ix(1));
        metrics.final_max_sidelobe_phi_deg = rad2deg(pL(ix(1)));
    end

    % ---- 2D and 3D gains at both foci ----
    % Numerators are exact field evaluations from A_total; denominators
    % are pattern integrals of the same unscaled field, so the ratios are
    % interpolation-free and scale-consistent.
    if pattern_ok
        I2 = trapz(phi_mesh, abs(F_eval).^2, 2);
        F0_2d_1 = local_F2d(phi_0_1, A_total, x, y, k0);
        F0_2d_2 = local_F2d(phi_0_2, A_total, x, y, k0);
        metrics.final_gain2D_1 = 10*log10((abs(F0_2d_1).^2 * 4*pi) / I2);
        metrics.final_gain2D_2 = 10*log10((abs(F0_2d_2).^2 * 4*pi) / I2);

        F3D_field = local_F3D(phi_mesh, theta_mesh, A_total, x, y, z, k0);
        I3 = trapz(theta_mesh, trapz(phi_mesh, abs(F3D_field).^2 .* sin(theta_mesh), 2));
        F0_3d_1 = local_F3D_point(phi_0_1, theta_0, A_total, x, y, z, k0);
        F0_3d_2 = local_F3D_point(phi_0_2, theta_0, A_total, x, y, z, k0);
        metrics.final_gain3D_1 = 10*log10((abs(F0_3d_1).^2 * 4*pi) / I3);
        metrics.final_gain3D_2 = 10*log10((abs(F0_3d_2).^2 * 4*pi) / I3);
    else
        metrics.final_gain2D_1 = NaN; metrics.final_gain2D_2 = NaN;
        metrics.final_gain3D_1 = NaN; metrics.final_gain3D_2 = NaN;
    end

    % ---- Main-beam skews ----
    d1 = phi_0_1 - metrics.Big_phi_final_1;
    d2 = phi_0_2 - metrics.Big_phi_final_2;
    metrics.main_beam_angle_final_1           = metrics.Big_phi_final_1;
    metrics.main_beam_angle_final_2           = metrics.Big_phi_final_2;
    metrics.main_beam_skew_final_1_signed     = atan2(sin(d1), cos(d1));
    metrics.main_beam_skew_final_2_signed     = atan2(sin(d2), cos(d2));
    metrics.main_beam_skew_final_1_signed_deg = rad2deg(metrics.main_beam_skew_final_1_signed);
    metrics.main_beam_skew_final_2_signed_deg = rad2deg(metrics.main_beam_skew_final_2_signed);
    metrics.main_beam_skew_final_1            = abs(metrics.main_beam_skew_final_1_signed);
    metrics.main_beam_skew_final_2            = abs(metrics.main_beam_skew_final_2_signed);
    metrics.main_beam_skew_final_1_deg        = rad2deg(metrics.main_beam_skew_final_1);
    metrics.main_beam_skew_final_2_deg        = rad2deg(metrics.main_beam_skew_final_2);

    % ---- Half-power beamwidths at both foci ----
    bw1 = local_beamwidth(Fmag, phi_mesh, metrics.Big_phi_final_1, metrics.Big_Val_final_1);
    bw2 = local_beamwidth(Fmag, phi_mesh, metrics.Big_phi_final_2, metrics.Big_Val_final_2);
    metrics.beamwidth_1     = bw1.beamwidth;
    metrics.beamwidth_2     = bw2.beamwidth;
    metrics.beamwidth_1_deg = rad2deg(bw1.beamwidth);
    metrics.beamwidth_2_deg = rad2deg(bw2.beamwidth);
    metrics.bw1_left_05     = bw1.left_05;
    metrics.bw1_right_05    = bw1.right_05;
    metrics.bw2_left_05     = bw2.left_05;
    metrics.bw2_right_05    = bw2.right_05;
end


% =========================================================================
% Local helpers (kept self-contained so this function works on a fresh
% path without depending on the nested helpers inside other solvers).
% Definitions match the conventions in perturb_method_v25 / Crammer.
% =========================================================================

function F = local_F2d(phi_loc, A_loc, x_loc, y_loc, k0_loc)
    A_loc = A_loc(:);
    x_loc = x_loc(:);
    y_loc = y_loc(:);
    phi_loc = phi_loc(:).';
    phase = k0_loc * (x_loc * cos(phi_loc) + y_loc * sin(phi_loc));
    F = A_loc.' * exp(1j * phase);
end


function F3D = local_F3D(phi_loc, theta_loc, A_loc, x_loc, y_loc, z_loc, k0_loc)
    % Includes the cos((pi/2)*cos(theta))/sin(theta) half-wave-dipole
    % element factor, matching the convention used by gain_calc_3D in
    % perturb_method_v25 and Crammer_Simultaneous_Constraints.
    % The in-plane phase matrix B is theta-independent, so it is hoisted
    % out of the loop (same optimization as Crammer's local_gain3D).
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
    % convention as local_F3D). Used for the gain numerators so foci
    % between mesh points are never interpolated.
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


function [peakVals, peakLocs] = local_findpeaks_circular(F, phi)
    % Vectorized circular peak finder: strict '>' against both circular
    % neighbors. Handles the 0/2pi seam exactly, needs no toolbox, and
    % matches the findpeaks_fast logic the solvers default to.
    F   = F(:).';
    phi = phi(:).';
    isPk = F > F([end 1:end-1]) & F > F([2:end 1]);
    peakVals = F(isPk);
    peakLocs = phi(isPk);
end


function v = local_interp_mag(phi_mesh, F_total, phi0)
    % Wrap-aware magnitude lookup on the open [0, 2*pi) mesh: append the
    % first sample at +2*pi so angles in the last segment interpolate
    % instead of extrapolating.
    phi0 = mod(phi0, 2*pi);
    v = abs(interp1([phi_mesh, phi_mesh(1) + 2*pi], ...
                    [F_total, F_total(1)], phi0, 'linear'));
end


function bw = local_beamwidth(Fmag, phi, pk_phi, pk_val)
    % Half-power (-3 dB) beamwidth of the lobe peaked at pk_phi, measured
    % relative to that lobe's OWN peak value pk_val (NOT the global max --
    % see the header note on the beamwidth convention). Circular search
    % outward from the peak in both directions with linear interpolation
    % of the crossing angle. Width is the arc left_05 -> right_05 through
    % the peak, so it is correct even for widths exceeding pi.
    Fmag = Fmag(:).';
    phi  = phi(:).';
    thr  = pk_val / sqrt(2);

    d = abs(atan2(sin(phi - pk_phi), cos(phi - pk_phi)));
    [~, i0] = min(d);

    bw.right_05 = local_halfpower_crossing(Fmag, phi, i0, +1, thr);
    bw.left_05  = local_halfpower_crossing(Fmag, phi, i0, -1, thr);
    if isnan(bw.left_05) || isnan(bw.right_05)
        bw.beamwidth = NaN;
    else
        bw.beamwidth = mod(bw.right_05 - bw.left_05, 2*pi);
    end
end


function ang = local_halfpower_crossing(Fmag, phi, i0, direction, thr)
    % Walk circularly from index i0 until the magnitude first drops below
    % thr; return the linearly interpolated crossing angle in [0, 2*pi).
    % NaN if the magnitude never drops below thr anywhere on the circle.
    M = numel(Fmag);
    i = i0;
    for step = 1:M-1
        j = mod(i - 1 + direction, M) + 1;
        if Fmag(j) < thr
            p1 = phi(i); p2 = phi(j);
            if direction == +1 && p2 < p1
                p2 = p2 + 2*pi;    % stepped across the 2*pi seam
            elseif direction == -1 && p2 > p1
                p2 = p2 - 2*pi;
            end
            ang = mod(p1 + (thr - Fmag(i)) * (p2 - p1) / (Fmag(j) - Fmag(i)), 2*pi);
            return;
        end
        i = j;
    end
    ang = NaN;
end
