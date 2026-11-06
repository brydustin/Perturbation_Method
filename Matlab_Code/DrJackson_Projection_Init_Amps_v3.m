%% Perturbative Method Code (Special Dipole Currents Version)
% Version 3:
% Optimized projection-based initial amplitudes.
% 4/30/2026
%
% Main optimization:
%   - Avoids the full O(N^2) pairwise distance matrix unless explicitly
%     requested. The amplitude rule only depends on adjacent emitters in
%     the projected sorted order, so the hot path is now O(N log N) from
%     sorting plus O(N) arithmetic.

function results = DrJackson_Projection_Init_Amps_v3(varargin)
%DRJACKSON_PROJECTION_INIT_AMPS_V3
%   Tight-beam closed-form array-factor initialization using projected
%   coordinates orthogonal to the focus direction.
%
%   Inputs:
%     x, y, phi_0
%
%   Name-value parameters:
%     'freq'                    default 3e9
%     'lambda_input'            default 3e8
%     'return_distance_matrices' default false
%
%   Outputs in results:
%     phase, phase_s
%     x_a, y_a, x_a_s, y_a_s
%     abs_I, abs_I_s
%     I
%     perm, invperm
%     neighbor_dist_s
%     D, D_s   (empty unless return_distance_matrices=true)

    p = inputParser;
    p.FunctionName = 'DrJackson_Projection_Init_Amps_v3';

    addRequired(p, 'x',     @isnumeric);
    addRequired(p, 'y',     @isnumeric);
    addRequired(p, 'phi_0', @isnumeric);

    addParameter(p, 'freq', 3e9, @isnumeric);
    addParameter(p, 'lambda_input', 3e8, @isnumeric);
    addParameter(p, 'return_distance_matrices', false, @islogical);

    parse(p, varargin{:});
    args = p.Results;

    x = args.x(:);
    y = args.y(:);
    phi_0 = mod(args.phi_0, 2*pi);
    freq = args.freq;
    lambda_input = args.lambda_input;
    return_distance_matrices = args.return_distance_matrices;

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

    % Coordinates after projection away from the steering direction.
    x_a = x - proj .* cphi;
    y_a = y - proj .* sphi;

    % Sort along the projected transverse line.
    [~, perm] = sortrows([y_a, x_a], [1 2]);
    x_a_s = x_a(perm);
    y_a_s = y_a(perm);
    phase_s = phase(perm);

    % Adjacent distances in sorted order are all that the amplitude
    % construction needs.
    dx_adj = diff(x_a_s);
    dy_adj = diff(y_a_s);
    neighbor_dist_s = hypot(dx_adj, dy_adj);

    if any(neighbor_dist_s == 0)
        error('Adjacent projected emitters coincide; amplitudes would divide by zero.');
    end

    abs_I_s = zeros(N, 1);
    abs_I_s(1) = 1 / neighbor_dist_s(1);
    abs_I_s(N) = 1 / neighbor_dist_s(end);
    if N > 2
        abs_I_s(2:N-1) = 0.5 * (neighbor_dist_s(2:end) + neighbor_dist_s(1:end-1));
    end

    I_s = abs_I_s .* exp(1i * phase_s);

    invperm = zeros(N, 1);
    invperm(perm) = (1:N).';

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
    results.D = D;
    results.D_s = D_s;
    results.abs_I = abs_I;
    results.abs_I_s = abs_I_s;
    results.I = I;
    results.perm = perm;
    results.invperm = invperm;
    results.neighbor_dist_s = neighbor_dist_s;
    results.freq = freq;
    results.lambda = lambda;
    results.k0 = k0;
    results.phi_0 = phi_0;
end
