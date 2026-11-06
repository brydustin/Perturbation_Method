%% Perturbative Method Code (Special Dipole Currents Version)
% Version 4:
% Jackson narrow-beam initialization with tie-aware aperture grouping.
% 4/30/2026
%
% This version follows "Dipole Currents for Narrow Beam.pdf" more closely:
%   1. Project dipoles onto the aperture plane orthogonal to phi_0.
%   2. Order aperture points monotonically along that plane.
%   3. Merge coincident / near-coincident projected points into groups.
%   4. Compute the aperture amplitudes from group-to-group spacing.
%   5. Split each group amplitude evenly across the dipoles in that group.
%
% Compared with v2/v3:
%   - Handles ties in projected position robustly.
%   - Uses endpoint amplitudes proportional to endpoint spacing, matching
%     Eqs. (10) and (12) in the PDF.
%   - Avoids O(N^2) distance work unless explicitly requested.

function results = DrJackson_Projection_Init_Amps_v4(varargin)
%DRJACKSON_PROJECTION_INIT_AMPS_V4
%   Compute projection-based initial currents for a narrower starting beam.
%
%   Required inputs:
%     x, y, phi_0
%
%   Name-value parameters:
%     'freq'                     default 3e9
%     'lambda_input'             default 3e8
%     'tie_tol'                  default [] (auto-scaled from geometry)
%     'split_rule'               'equal' only
%     'return_distance_matrices' default false
%
%   Output fields:
%     I, abs_I, phase
%     x_a, y_a
%     perm, invperm
%     group_id_sorted, group_members, group_sizes
%     x_a_group, y_a_group, group_spacing
%     abs_I_group
%     D, D_s (empty unless requested)

    p = inputParser;
    p.FunctionName = 'DrJackson_Projection_Init_Amps_v4';

    addRequired(p, 'x',     @isnumeric);
    addRequired(p, 'y',     @isnumeric);
    addRequired(p, 'phi_0', @isnumeric);

    addParameter(p, 'freq', 3e9, @isnumeric);
    addParameter(p, 'lambda_input', 3e8, @isnumeric);
    addParameter(p, 'tie_tol', [], @isnumeric);
    addParameter(p, 'split_rule', 'equal', @(s) ischar(s) || isstring(s));
    addParameter(p, 'return_distance_matrices', false, @islogical);

    parse(p, varargin{:});
    args = p.Results;

    x = args.x(:);
    y = args.y(:);
    phi_0 = mod(args.phi_0, 2*pi);
    freq = args.freq;
    lambda_input = args.lambda_input;
    tie_tol = args.tie_tol;
    split_rule = lower(string(args.split_rule));
    return_distance_matrices = args.return_distance_matrices;

    if split_rule ~= "equal"
        error('Unsupported split_rule "%s". Only "equal" is implemented.', split_rule);
    end

    N = numel(x);
    if N < 2
        error('x,y must contain at least two elements.');
    end

    lambda = lambda_input / freq;
    k0 = 2*pi / lambda;

    cphi = cos(phi_0);
    sphi = sin(phi_0);

    proj = x * cphi + y * sphi;
    phase = -k0 * proj;

    % Aperture-plane coordinates from Eqs. (15)-(16) in the PDF.
    x_a = x - proj .* cphi;
    y_a = y - proj .* sphi;

    % Sort so the aperture points progress monotonically along the
    % transverse line. We use y_a first, x_a second, matching earlier code.
    [~, perm] = sortrows([y_a, x_a], [1 2]);
    x_a_s = x_a(perm);
    y_a_s = y_a(perm);
    phase_s = phase(perm);

    invperm = zeros(N, 1);
    invperm(perm) = (1:N).';

    % Work in a 1D coordinate along the aperture line. Any unit tangent
    % orthogonal to the steering direction is valid.
    t_hat = [-sphi; cphi];
    s_coord = x_a_s * t_hat(1) + y_a_s * t_hat(2);

    if isempty(tie_tol)
        geom_scale = max(1, max(abs([x; y])));
        tie_tol = 1e-10 * geom_scale;
    end
    if tie_tol < 0
        error('tie_tol must be nonnegative.');
    end

    % Group consecutive projected points whose aperture coordinates coincide
    % up to tolerance. This treats ties as a single aperture location.
    group_id_sorted = zeros(N, 1);
    group_id_sorted(1) = 1;
    num_groups = 1;
    for k = 2:N
        if abs(s_coord(k) - s_coord(k-1)) <= tie_tol
            group_id_sorted(k) = num_groups;
        else
            num_groups = num_groups + 1;
            group_id_sorted(k) = num_groups;
        end
    end

    if num_groups < 2
        error(['All projected aperture points collapsed into one group at phi_0 = %.6f rad. ' ...
               'The Jackson spacing construction is undefined for this geometry.'], phi_0);
    end

    group_members = accumarray(group_id_sorted, (1:N).', [num_groups, 1], @(idx) {idx});
    group_sizes = cellfun(@numel, group_members);

    x_a_group = zeros(num_groups, 1);
    y_a_group = zeros(num_groups, 1);
    s_group = zeros(num_groups, 1);
    phase_group = zeros(num_groups, 1);
    for g = 1:num_groups
        idx = group_members{g};
        x_a_group(g) = mean(x_a_s(idx));
        y_a_group(g) = mean(y_a_s(idx));
        s_group(g) = mean(s_coord(idx));
        phase_group(g) = mean(phase_s(idx));
    end

    % Since groups are aperture locations, their spacing is the quantity
    % used in Eqs. (9)-(12).
    group_spacing = diff(s_group);
    if any(group_spacing <= tie_tol)
        error('Grouped aperture spacing is still degenerate; tie_tol may be too small.');
    end

    abs_I_group = zeros(num_groups, 1);
    abs_I_group(1) = group_spacing(1);
    abs_I_group(num_groups) = group_spacing(end);
    if num_groups > 2
        abs_I_group(2:num_groups-1) = ...
            0.5 * (group_spacing(1:end-1) + group_spacing(2:end));
    end

    % Split each aperture-location amplitude evenly among the tied dipoles.
    abs_I_s = zeros(N, 1);
    for g = 1:num_groups
        idx = group_members{g};
        abs_I_s(idx) = abs_I_group(g) / group_sizes(g);
    end

    I_s = abs_I_s .* exp(1i * phase_s);

    abs_I = abs_I_s(invperm);
    I = I_s(invperm);
    phase = phase_s(invperm);

    D = [];
    D_s = [];
    if return_distance_matrices
        XYa_s = [x_a_s, y_a_s];
        D_s = pdist2(XYa_s, XYa_s);
        D = D_s(invperm, invperm);
    end

    results.phase = phase;
    results.phase_s = phase_s;
    results.x_a = x_a;
    results.y_a = y_a;
    results.x_a_s = x_a_s;
    results.y_a_s = y_a_s;
    results.s_coord_s = s_coord;
    results.perm = perm;
    results.invperm = invperm;
    results.group_id_sorted = group_id_sorted;
    results.group_members = group_members;
    results.group_sizes = group_sizes;
    results.num_groups = num_groups;
    results.x_a_group = x_a_group;
    results.y_a_group = y_a_group;
    results.s_group = s_group;
    results.group_spacing = group_spacing;
    results.phase_group = phase_group;
    results.abs_I_group = abs_I_group;
    results.abs_I = abs_I;
    results.abs_I_s = abs_I_s;
    results.I = I;
    results.D = D;
    results.D_s = D_s;
    results.freq = freq;
    results.lambda = lambda;
    results.k0 = k0;
    results.phi_0 = phi_0;
    results.tie_tol = tie_tol;
    results.split_rule = char(split_rule);
end
