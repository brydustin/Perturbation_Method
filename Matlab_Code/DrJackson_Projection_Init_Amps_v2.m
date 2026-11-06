%% Perturbative Method Code (Special Dipole Currebts Version)
% Version 1:
% Contains code for initial amplitudes for producing tighter beams at
% initial point.
% 1/27/2026
% Dependencies:
%
% Version Update: Initial version
%
function results = initial_amps_calc_v2(varargin)
% -------------------------------------------------------------------------
%   Tight-Beam Closed-Form Array Factor Generator
%
%   x_n^a = x_n - (x_n cos(phi_0) + y_n sin(phi_0)) cos(phi_0)
%   y_n^a = y_n - (x_n cos(phi_0) + y_n sin(phi_0)) sin(phi_0)  
%
%   Delta_{n,m} = sqrt( (x_n^a - x_m^a)^2 + (y_n^a - y_m^a)^2 )
%
%   |I_n| = (Delta_{n,n+1} + Delta_{n,n-1})/2   %N \neq (1,N)
%            Delta_1 = 1/Delta_{1,2}
%            Delta_N = 1/Delta_{N,N-1}
%
%   phi_n = k0 * (x_n * cos(phi_0) + y_n * sin(phi_0))
% -------------------------------------------------------------------------
% Outputs:
%   I :a vector of length N of calculated inition amplitudes

    %% ---- Handle input arguments ----
    p = inputParser;
    p.FunctionName = 'perturb_method_2_beam_v1';

    % Required inputs
    addRequired(p, 'x',        @isnumeric); % vector of x coordinates
    addRequired(p, 'y',        @isnumeric); % vector of y coordinates
    addRequired(p, 'phi_0',    @isnumeric); % first focus direction (in radians)

    % Optional inputs (name–value pairs; make sure to use "addParameter")
    addParameter(p, 'freq',         3e9, @isnumeric);
    addParameter(p, 'lambda_input', 3e8, @isnumeric);

    % ----- Parse everything -----
    parse(p, varargin{:});
    args = p.Results;

    % Extract into local variables
    x               = args.x(:);
    y               = args.y(:);
    phi_0           = args.phi_0;
    freq            = args.freq;
    lambda_input    = args.lambda_input;

    %% ---- Modify Input Angles to conform to Polar Space ----
    phi_0 = mod(phi_0, 2*pi);
    
    %% ---- Initialize Basic RF parameters ----
    %freq   = 3e9;
    %lambda = 3e8 / freq;
    lambda = lambda_input / freq;
    k0     = 2*pi / lambda;

    %% ---- Initialize Drone(Emitter) Position Geometry ----
    x = x(:); % Ensure column vector
    y = y(:); % Ensure column vector
    N = numel(x);

    if N < 2    % error handling
        error('x,y must contain at least two elements.');
    end

    %% ---- Compute steering phase term  ----
    phase = -k0 * (x*cos(phi_0) + y*sin(phi_0));   % steering to focus

    %% ---- Compute x_a for n = 1..N ----
    x_a = x - (x*cos(phi_0) + y*sin(phi_0)).*cos(phi_0);
    y_a = y - (x*cos(phi_0) + y*sin(phi_0)).*sin(phi_0);

    %% ---- Compute the new ordering for x_a
    % Sort indices by y_a (ascending), tie-break on x_a (optional)
    [~, perm] = sortrows([y_a, x_a], [1 2]);
    
    % Work in sorted order (do NOT touch x,y)
    x_a_s   = x_a(perm);
    y_a_s   = y_a(perm);
    phase_s = phase(perm);


    %% ---- Compute D(n,m) for n,m = 1..N (pairwise euclidian distance) ----
    %D = pdist2(x_a, y_a);
    % Distances in sorted order
    XYa = [x_a_s, y_a_s];
    D_s = pdist2(XYa, XYa);

    %% ---- Compute Abs_In
    %abs_I = zeros(size(x));
    %abs_I(1) = 1/D(1,2);
    %abs_I(N) = 1/D(N,N-1);
    %for i = 2:(N-1)
    %    abs_I(i) = (D(i,i+1) + D(i,i-1))/2;
    %end

    % abs_I and I in sorted order
    abs_I_s      = zeros(N,1);
    abs_I_s(1)   = 1 / D_s(1,2);
    abs_I_s(N)   = 1 / D_s(N,N-1);
    for ii = 2:(N-1)
        abs_I_s(ii) = (D_s(ii,ii+1) + D_s(ii,ii-1)) / 2;
    end
    I_s = abs_I_s .* exp(1i*phase_s);


    %% ---- Compute In
    %I = abs_I .* exp(i*phase);
    
    % Inverse permutation to return to original order
    invperm = zeros(N,1);
    invperm(perm) = (1:N).';
    
    abs_I = abs_I_s(invperm);
    I     = I_s(invperm);
    phase = phase_s(invperm);

    % Optional: D in original indexing
    D = D_s(invperm, invperm);



    %% ---- Results ----
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


end

