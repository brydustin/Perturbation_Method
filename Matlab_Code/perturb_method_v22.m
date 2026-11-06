%% Perturbative Method Code
% Version 22:
% Contains code for beam-focussing with one focus
% and optionally with either zero or one nulls.
% 4/6/2025
% Dependencies: Uses plot_pattern_v5.m, directivity_met_v2.m
%
% Version Update: Adding correction for F3D function and Gain calculation.
%
function results = perturb_method_v22(varargin)
%function results = perturb_method_v22(Max_iter, eps_dB, x, y, phi_0, show_plots, save_plots, save_final_plot, null_phi, verbose)
% PERTURB_METHOD_V20
%
% Behaviour: Following the method outlined in the Mosier paper:
%   - The algorythm steers a main beam in the focus direction phi_0.
%   - Each epoch:
%       * finds all sidelobes (peaks excluding main beam),
%       * selects the WORST sidelobe (max dB),
%       * applies a single correction targeted at that sidelobe.
%   - If a null direction is provided:
%       * element 1 is reserved for the null (unused in sidelobe corrections),
%       * after sidelobes are below eps_dB or Max_iter reached,
%         element 1 is used to synthesize a null at null_phi.
%   - If no null direction is provided:
%       * all elements are used for sidelobe corrections;
%         no null is enforced.
%   - Per-epoch printing is controlled by 'verbose' (default: false).
%
% Outputs:
%   results.final_epoch
%   results.total_time
%   results.focus_angle
%   results.focus_angle_deg
%   results.null_angle   (empty if no null)
%   results.null_angle_deg
%   results.max_sidelobe_store
%   results.max_side_phi_store
%   results.directivity_metric_1_beamwidth_store
%   results.final_function
%   results.A_eff = A_eff;
%   results.delta_eff = delta_eff;

% Note: The "1" in directivity_metric_1_beamwidth_store refers to the
% type (half-power), not the version number.


% Too Do List:
%???

    %% ---- Handle input arguments ----
    p = inputParser;
    p.FunctionName = 'perturb_method_v20';

    % Required inputs
    addRequired(p, 'Max_iter', @isnumeric);
    addRequired(p, 'eps_dB',   @isnumeric);
    addRequired(p, 'x',        @isnumeric);
    addRequired(p, 'y',        @isnumeric);
    addRequired(p, 'phi_0',    @isnumeric);

    % Optional inputs (name–value pairs)
    addOptional(p, 'z',                    [], @isnumeric);
    addOptional(p, 'A_init',               [], @isnumeric);
    addOptional(p, 'null_phi',             [], @isnumeric);
    addOptional(p, 'show_plots',        false, @islogical);
    addOptional(p, 'show_plot_raw',     false, @islogical);
    addOptional(p, 'show_plot_init',    false, @islogical);
    addOptional(p, 'show_plots_st7',    false, @islogical);
    addOptional(p, 'show_plots_st12',   false, @islogical);
    addOptional(p, 'show_plots_st16',   false, @islogical);
    addOptional(p, 'show_final_plot',   false, @islogical);
    %addOptional(p, 'save_plots',       false, @islogical);
    %addOptional(p, 'save_final_plot',  false, @islogical);
    addOptional(p, 'verbose',           false, @islogical);
    addOptional(p, 'full_loop',         false, @islogical); %for whether to loop over all sidelobes
    addOptional(p, 'const_null_update', false, @islogical); %for whether to always update the null
    addParameter(p, 'cone_rad',            [], @isnumeric);   % for cone boundaries
    addOptional(p, 'return_funcs',      false, @islogical);
    addOptional(p, 'theta_0',             pi.*0.5, @isnumeric);

    % ----- Parse everything -----
    parse(p, varargin{:});
    args = p.Results;

    % Extract into local variables
    Max_iter        = args.Max_iter;
    eps_dB          = args.eps_dB;
    x               = args.x(:);
    y               = args.y(:);
    z               = args.z(:);
    phi_0           = args.phi_0;
    cone_rad        = args.cone_rad;

    
    null_phi        = args.null_phi;
    show_plots      = args.show_plots;
    show_plot_raw   = args.show_plot_raw;
    show_plot_init  = args.show_plot_init;
    show_plots_st7  = args.show_plots_st7;
    show_plots_st12 = args.show_plots_st12;
    show_plots_st16 = args.show_plots_st16;
    show_final_plot = args.show_final_plot;
    %save_plots      = args.save_plots;
    %save_final_plot = args.save_final_plot;
    verbose         = args.verbose;
    full_loop       = args.full_loop;
    const_null_update = args.const_null_update;
    A_init          = args.A_init;
    return_funcs      = args.return_funcs;    
    theta_0           = args.theta_0;

    %% ---- Modify Input Angles to conform to Polar Space ----
    phi_0 = mod(phi_0, 2*pi);
    theta_0 = mod(theta_0, 2*pi);
    null_phi = mod(null_phi, 2*pi);
    %phi_s = mod(phi_s, 2*pi);
    %peakLocs = mod(peakLocs, 2*pi);

    %% ---- Initialize Special Script Variables
    outdir = 'D:\Research\Dr. Onofreis projects\DS MATLAB CODE\Github_Shared_Code\Relay-Phased-Array-Optimization-main\Plot_Saves';
    use_null = ~(isempty(null_phi) || any(isnan(null_phi)));

    %% ---- Initialize Basic RF parameters ----
    freq   = 3e9;
    lambda = 3e8 / freq;
    k0     = 2*pi / lambda;

    %% ---- Initialize Drone(Emitter) Position Geometry ----
    x = x(:); % Ensure column vector
    y = y(:); % Ensure column vector
    N = numel(x);

    if N < 2    % error handling
        error('x,y must contain at least two elements.');
    end
    if ~isempty(A_init) && ((numel(A_init) ~= N )&&(numel(A_init) ~= N-1 ))
        error('A_init must be the same length N (or N-1) as the number of dipole positions.')
    end

    %% ---- Other Basic Variables ----
    center_idx = 1;     % reserve element 1 if using a null
    outer_idx  = setdiff(1:N, center_idx);

    % Evaluation grid (for computing the pattern)
    mesh_len = 1000; % length of phi-mesh for plotting pattern
    %phi = linspace(0, 2*pi, 1000); %original
    % Deliberatly remove 2pi endpoint
    %phi = linspace(0, 2*pi, 1000+1);
    phi = linspace(0, 2*pi, mesh_len+1);
    phi(end) = [];   % remove 2pi duplicate
    theta_mesh = linspace(0, pi, mesh_len);

    %% ---- Build the F2D Function ----
    function F = F2d(phi_loc, A_loc, x_loc, y_loc, delta_loc, k0_loc)
    % F2d  Compute the 2D array factor of an antenna array.
    % Inputs:
    %   phi_loc   - vector of azimuth angles (radians)
    %   A_loc     - Nx1 complex vector of element amplitudes
    %   x_loc, y_loc  - Nx1 vectors of element coordinates (meters)
    %   delta_loc - Nx1 phase offsets (radians). If empty, assumed zeros.
    %   k0_loc    - wavenumber = 2*pi/lambda
    % Output:
    %   F     - complex field pattern evaluated at each phi
        if nargin < 6   % error handling
            error('F2d: need phi, A, x, y, delta, k0');
        end
        % Ensure column vectors
        A_loc = A_loc(:);
        x_loc = x_loc(:);
        y_loc = y_loc(:);
        if isempty(delta_loc) % Initialize zero delta if needed
            delta_loc = zeros(size(A_loc));
        else
            delta_loc = delta_loc(:);
        end
        phi_loc = phi_loc(:).';  % 1xM row vector for broadcasting
        % phase term for each element and angle: N x M phase matrix
        phase = k0_loc * (x_loc * cos(phi_loc) + y_loc * sin(phi_loc)) + delta_loc;        
        F = A_loc.' * exp(1j * phase);  % 1 x M
    end

    %% ---- Build the F3D Function ----
    function F = F3D(phi_loc, theta_loc, A_loc, x_loc, y_loc, z_loc, delta_loc, k0_loc)
    % F2d  Compute the 2D array factor of an antenna array.
    % NOTE: Only use for evaluating 3D gain. Do not use for beamforming.
    %
    % Inputs:
    %   phi_loc   - vector of azimuth angles (radians)
    %   A_loc     - Nx1 complex vector of element amplitudes
    %   x_loc, y_loc  - Nx1 vectors of element coordinates (meters)
    %   delta_loc - Nx1 phase offsets (radians). If empty, assumed zeros.
    %   k0_loc    - wavenumber = 2*pi/lambda
    % Output:
    %   F     - complex field pattern evaluated at each phi
        if nargin < 8   % error handling
            error('F3d: need phi, theta, A, x, y, z, delta, k0');
        end
        
        % Ensure column vectors
        A_loc = A_loc(:);
        x_loc = x_loc(:);
        y_loc = y_loc(:);

        if isempty(z_loc) % Initialize zero zs if needed
            z_loc = zeros(size(A_loc));
        else
            z_loc = z_loc(:);
        end

        if isempty(delta_loc) % Initialize zero delta if needed
            delta_loc = zeros(size(A_loc));
        else
            delta_loc = delta_loc(:);
        end

        % Angle grids        
        phi_loc = phi_loc(:).';  % 1xM row vector for broadcasting
        % phase term for each element and angle: N x M phase matrix
        theta_loc = theta_loc(:).'; % Lx1 

        % Create meshgrid
        [PHI, THETA] = meshgrid(phi_loc, theta_loc);  % L x M

        % Compute phase: N x L x M

        % Reshape for broadcasting
        x = reshape(x_loc, [], 1, 1);   % [N x 1 x 1]
        y = reshape(y_loc, [], 1, 1);
        z = reshape(z_loc, [], 1, 1);
        delta = reshape(delta_loc, [], 1, 1);

        TH = reshape(THETA, 1, size(THETA,1), size(THETA,2)); % [1 x L x M]
        PH = reshape(PHI,   1, size(PHI,1),   size(PHI,2));   % [1 x L x M]

        %phase = k0_loc * (...
        %    x_loc .* sin(THETA) .* cos(PHI) + ...
        %    y_loc .* sin(THETA) .* sin(PHI) + ...
        %    z_loc .* cos(THETA)) ...
        %    + delta_loc;  
        phase = k0_loc * (...
            x .* sin(TH) .* cos(PH) + ...
            y .* sin(TH) .* sin(PH) + ...
            z .* cos(TH)) ...
            + delta;          
        
        % Other components
        E = cos((pi/2) * cos(TH)) ./ sin(TH);
        E(~isfinite(E)) = 0;   % handles NaN and Inf

        % Sum over elements
        %F = A_loc.' .* exp(1j * phase);  % L x M (theta × phi)
        A = reshape(A_loc, [], 1, 1);
        F = sum(A .* E .* exp(1j * phase), 1);
        F = squeeze(F);

    end

    %% ---- Build Function to fix Matlabs Findpeaks for polar maps ----
    function [peakVals, peakLocs] = findpeaks_circular(Fmag, phi_vec)
    % FINDPEAKS_CIRCULAR  Find local maxima on a circular domain (phi in radians).
    %   [peakVals, peakLocs] = findpeaks_circular(Fmag, phi)
    %   - Fmag : 1xM vector of magnitudes (or Mx1)
    %   - phi_vec  : 1xM vector of angles in radians (monotonic, usually 0..2*pi)
    %   Returns:
    %   - peakVals : values of detected peaks
    %   - peakLocs : corresponding angles in [0,2*pi)
    %
    % This handles the wrap-around at 0/2pi by making a small extension on both
    % sides, ensuring the X vector passed to findpeaks is strictly increasing.
        % Ensure row vectors
        Fmag    = Fmag(:).';
        phi_vec = phi_vec(:).';

        M = numel(phi_vec);
        if numel(Fmag) ~= M % error handling
            error('findpeaks_circular: phi and Fmag size mismatch');
        end
        % Remove duplicate 2π endpoint if present
        if abs(phi_vec(end) - phi_vec(1) - 2*pi) < 1e-8
            phi_vec = phi_vec(1:end-1);
            Fmag    = Fmag(1:end-1);
        end
        % Ensure strictly increasing phi
        if any(diff(phi_vec) <= 0)
            [phi_vec, idx] = sort(phi_vec);
            Fmag = Fmag(idx);
        end
        % Pick a small extension length (3 points each side is enough)
        %ne = min(3, numel(phi_vec)-1);
        ne = min(50, numel(phi_vec)-1); %do 50 and see what happerns
        % Build wrapped arrays (strictly increasing)
        phi_left  = phi_vec(end-ne+1:end) - 2*pi;
        phi_right = phi_vec(1:ne) + 2*pi;
        phi_circ  = [phi_left, phi_vec, phi_right];
        
        Fmag_left  = Fmag(end-ne+1:end);
        Fmag_right = Fmag(1:ne);
        Fmag_circ  = [Fmag_left, Fmag, Fmag_right];

        % now phi_circ is strictly increasing by construction
        % call findpeaks with X = phi_circ
        [pv, pl_circ] = findpeaks(Fmag_circ, phi_circ);
        pl = mod(pl_circ, 2*pi); % wrap angles back into [0,2*pi)

        % Sort and remove duplicates that may appear because of extension:
        % If a peak appears at (say) phi=0 and also at phi=2*pi, mod collapses both to 0.
        % Keep unique peaks by angle (within tolerance)        
        [pl_sorted, idx] = sort(pl);
        pv_sorted = pv(idx);

        keep = true(size(pl_sorted));
        tol = 1e-6;
        for k = 2:numel(pl_sorted)
            if abs(pl_sorted(k) - pl_sorted(k-1)) < tol
                if pv_sorted(k) <= pv_sorted(k-1) % keep the one with larger pv
                    keep(k) = false;
                else
                    keep(k-1) = false;
                end
            end
        end

        peakLocs = pl_sorted(keep).';
        peakVals = pv_sorted(keep).';

        % ensure column outputs for compatibility with existing code
        %peakLocs = peakLocs(:);
        %peakVals = peakVals(:);
    end

   
    %% ---- Build (Stable) Angle Difference Function ----
    function d = ang_diff(a, b)
    % ANG_DIFF Find angular diffrence between to directions on a circular domain (in radians).
    %   d = ang_diff(a, b)
    %   [~, mainIdx] = min(ang_diff(peakLocs, phi_0));
    %   - a,b : angles in radians
    %   Returns:
    %   - d : angular distance
    %
    %   This handles the wrap-around at 0/2pi by using the atan2 function
        %d = abs(atan2(sin(a - b), cos(a - b))); %original
        raw = atan2(sin(a - b), cos(a - b));
        d = abs(raw);
    
        tol = 1e-12; %tolarance theshold
    
        % Debug trigger
        idx = (d < tol) & (d > 0); %index which angle inputs trigger
        if any(idx)
            fprintf('Tiny angle diff detected: %g\n', d(idx));
        end

    d(d < tol) = 0; % enforce zeros for values below tolarance
    end

    %% Function to calculate Gain (2D Version)
    % Version 1:
    % Contains code for calculating Gain given a pattern, the phi_mesh for that
    % pattern, and a direction phi0.
    % 3/15/2026
    %
    function G = gain_calc(F_total, phi_mesh, phi_0)
        % input the calculated f_total, the phi_mesh, and the target direction
        % phi0 to calculate Gain in that direction.
        
        phi_mesh = phi_mesh(:).'; % Ensure correct shape
    
        % Total radiated power (integrate over phi)
        I = trapz(phi_mesh, abs(F_total).^2, 2);
    
        % Peak value at phi0 
        F_at_phi_0 = interp1(phi_mesh, F_total.', phi_0, 'linear', 'extrap').';
        
        % Gain formula
        %G = 10*log((F_at_phi_0.^2 * 4*pi)./I); %original (possibly wrong) 
        G = 10*log10((F_at_phi_0.^2 * 4*pi)./I);
    end    

    %% Function to calculate Gain (3D Version)
    % Version 1:
    % Contains code for calculating Gain given a pattern, the phi_mesh for that
    % pattern, and a direction phi0.
    % 4/6/2026
    %
    function G3D = gain_calc_3D(F_total, phi_mesh, theta_mesh, phi_0, theta_0)
        % input the calculated f_total, the angle meshes, and the target
        % directions phi0, theta0 to calculate Gain in that direction.
        
         % Ensure correct shapes
        phi_mesh = phi_mesh(:).';  % 1 x M
        theta_mesh = theta_mesh(:);   % L x 1

        % Power pattern
        P = abs(F_total).^2;   % L x M
        P(~isfinite(P)) = 0;   % handles NaN and Inf

        % Apply spherical weighting
        sin_theta = sin(theta_mesh);   % L x 1
        P_weighted = P .* sin_theta;   % broadcast across phi   

        % Integrate over phi first
        I_phi = trapz(phi_mesh, P_weighted, 2);   % L x 1        

        % Integrate over theta second
        I = trapz(theta_mesh, I_phi);   % scalar

        % Interpolate peak value at (phi_0, theta_0)
        % 2D interpolation
        F0 = interp2(phi_mesh, theta_mesh, F_total, phi_0, theta_0, 'linear');

%        % Peak value at phi0 
%        F_at_phi_0 = interp1(phi_mesh, F_total.', phi_0, 'linear', 'extrap').';
        
        % Gain formula
        %G = 10*log((F_at_phi_0.^2 * 4*pi)./I);
        G3D = 10*log10( (abs(F0).^2 * 4*pi) / I );
    end  
    
    %% ---- Test the F2D function (Optional) ----
    if (show_plots || show_plot_raw)
        if ~isempty(A_init) && (numel(A_init) == N )
            A = A_init;
        else % remember to come back and handle null case later
            A = ones(N,1);
        end

        %A = ones(N,1);
        A = A(:);
        delta = zeros(N,1);
        F1 = F2d(phi, A, x, y, delta, k0);  % returns 1xnumel(phi) complex vector
        %Fdb1 = 10*log10(abs(F1).^2 / max(abs(F1).^2)); % decibel conversion
        
        %lab_1 = "Initial Pattern (No Focusing)";
        lab_1 = "Raw Geometric Pattern (No Beam Directing)";
        % View function graph
        plot_pattern_v5(phi, F1, 'label',lab_1, 'show_plots', true, 'iter', -1 );

             
    end

    %% ---- Begin the Algorithm ---- 
    
    % Preliminary: 
    tic; % Start computation timer
    iter = 0; % Initialize iteration counter

    % Preliminary: Reserve center node for Null case
    if use_null %Null direction case
        if ~isempty(A_init) && (numel(A_init) == N-1) %assume len(A)=N-1
            % Center off; used later for null synthesis
            A0 = [0 A_init]; %Initialize for storage
            A0(center_idx) = 0;
        elseif ~isempty(A_init) && (numel(A_init) == N)
            error('For Null version, A_init must be length N-1.')
        else
            % Center off; used later for null synthesis
            A0 = ones(N,1); %Initialize for storage
            A0(center_idx) = 0;
        end
    else % No Null directions case
        if ~isempty(A_init) && (numel(A_init) == N)%assume len(A)=N
            % Center on; used for non-null case
            %A0 = ones(N,1); %Initialize for storage
            A0 = A_init; %Initialize for storage
        elseif ~isempty(A_init) && (numel(A_init) == N-1) %assume len(A)=N-1
            error('For Non-Null version, A_init must be length N.')
        else
            A0 = ones(N,1); %Initialize for storage
        end
    end

    delta0 = -k0 * (x*cos(phi_0) + y*sin(phi_0));   % steering to focus



    %% ---- Pre-allocate storage for reconstruction and max sidelobe tracking ----
    max_sidelobe_store = nan(Max_iter+1,1); % for max sidelobe value
    max_side_phi_store = nan(Max_iter+1,1); % for max sidelobe direction
    directivity_metric_1_beamwidth_store = nan(Max_iter+1,1); % for directivity metric_1
    main_peakLoc_store = nan(Max_iter+1,1); % for main peak direction
    main_peakVal_store = nan(Max_iter+1,1); % for main peak value
    focus_value_store = nan(Max_iter+1,1); % for value in focus direction
    focus_value_store_dB = nan(Max_iter+1,1); % for value in focus direction in dB form
    G2D_store = nan(Max_iter+1,1); % for value in focus direction
    G3D_store = nan(Max_iter+1,1); % for value in focus direction
    main_peak_skew = nan(Max_iter+1,1); % for deviation betweem the main peak angle and focus direction
    %A_eff_store = nan(Max_iter+1,N); % for the effective A values calculated at each iteration
    
    % Record Final value at focus angle
    %    focus_value_store(1) = interp1(phi, F_total, phi_0, 'linear', 'extrap');

    % Pre-Allocate storage for conditional tracking
    % for return_funcs = true
    if (return_funcs)
        F_store = nan(Max_iter+1,mesh_len); % for storing the point values of the function iterates
        %F3d_store = nan(Max_iter+1, mesh_len, mesh_len); %BAD. Exceeds memory limit
    end

    % Store terms for reconstruction
    A_store     = {A0}; % cell array to store A vectors
    A_eff_store = {A0 .* exp(1j * delta0)}; % cell array for the effective A values calculated at each iteration
    %A_eff_store = {A0}; % cell array for the effective A values calculated at each iteration
    delta_store = {delta0}; % cell array to store delta vectors
    phi_store   = phi_0;


    %% ---- Steps 1-3 ----

    %% Step 1: Designate initial beam steering
    % (Set delta0; taken care of above before storage)

    %% Step 2: Declare A = 1s or 01s 
    % (taken care of above before storage)

    %% Step 3: Compute initial beam function (Initial total field)
    %A_eff_store(1) = A0; %record initial (effective) As
    F_total = F2d(phi, A0, x, y, delta0, k0);

    % Optional initial plot
    if (show_plots || show_plot_init)
        lab_2 = "Initial Pattern (with Focus)(Step 3)";
        % View function graph
        plot_pattern_v5(phi, F_total, 'label',lab_2, 'phi_0', phi_0, 'show_plots', true );
    end

    % Optional storage
    if (return_funcs)
        %F_store(1) = F_total; % record initial pattern
        F_store(1, :) = F_total(:).'; % record initial pattern
        %F_total = F2d(phi, A0, x, y, delta0, k0);
        %F_3D_total = F3D(phi, theta_mesh, A0, x, y, z, delta0, k0);
        %F3d_store(1,:,:) = F_3D_total;
        G2D_store(1) = gain_calc(F_total, phi, phi_0);
        G3D_store(1) = gain_calc_3D( ...
            F3D(phi, theta_mesh, A0, x, y, z, delta0, k0), ...
            phi, theta_mesh, phi_0, theta_0);
    end

    %% ---- Steps 4-7 ----
    %% Step 4: Identify all the local maxima for the function (thus all lobes including the focus)
    Fmag = abs(F_total);
    [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
    if isempty(peakVals) % error handeling
        if verbose
            fprintf('Iteration %d: no peaks found; stopping.\n', iter);
        end
    end
    peakLocs = mod(peakLocs, 2*pi);
    
    %% Step 5: Identifying which of the lobes is the largest (the focus). 
    %[~, mainIdx] = min(abs(peakLocs - phi_0)); %old method
    [~, mainIdx] = min(ang_diff(peakLocs, phi_0));
    
    %% Step 6: Identify and keep only sidelobes with peaks above the specified
    % Record the main beam for future analysis
    main_peakLoc_store(1) = peakLocs(mainIdx);
    main_peakVal_store(1) = peakVals(mainIdx);
    % Record main beam skew
    %main_peak_skew(1) = (phi_0-main_peakLoc_store(1)); %original
    main_peak_skew = atan2(sin(phi_0 - main_peakLoc_store(1)), cos(phi_0 - main_peakLoc_store(1)));
    % Record value at focus angle  for future analysis
    focus_value_store(1) = interp1(phi, F_total, phi_0, 'linear', 'extrap');
    focus_value_store_dB(1) = 10*log10( ...
        (interp1(phi, F_total, phi_0, 'linear', 'extrap').^2) / (max(Fmag).^2));
        
    %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
    % Remove the main beam from the list
    peakVals(mainIdx) = [];
    peakLocs(mainIdx)    = [];

    if isempty(peakVals) % if there are no other sidelobes
        if verbose
            fprintf('Iteration %d: no sidelobes; stopping.\n', iter);
        end
        Slobe = [];
        phi_s = [];
    elseif (~isempty(peakVals) && ~isempty(cone_rad)) % if there are designated conebounds
        peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        validMask_db = peakVals_db > eps_dB;
        % TEST CODE FOR CONE EXCLUSION
        % Smallest signed angle difference in (-pi, pi]
        d = mod(peakLocs - phi_0 + pi, 2*pi) - pi;
        % Logical mask: 1 (true) if outside cone_rad, else 0 (false)
        validMask_cone = abs(d) > cone_rad;   % logical array, same size as peakLocs
        %validMask_cone = %Code for identifying peaks inside cone bounds from focus phi_0
        
        validMask = validMask_cone & validMask_db;
        Slobe = peakVals_db(validMask);
        phi_s = peakLocs(validMask);
        % Sort sidelobes from largest to smallest
        [Slobe_sorted, sortIdx] = sort(Slobe, 'descend');
        Slobe = Slobe_sorted;
        % Reorder angles using the same sorting indices
        phi_s_sorted = phi_s(sortIdx);
        phi_s = phi_s_sorted;        
    else    % If there aren't conebounds
        peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        validMask = peakVals_db > eps_dB; %assigns 1 to sidelobes violating sidelobe goal condition
        Slobe = peakVals_db(validMask);
        phi_s = peakLocs(validMask);
        % Sort sidelobes from largest to smallest
        [Slobe_sorted, sortIdx] = sort(Slobe, 'descend');
        Slobe = Slobe_sorted;
        % Reorder angles using the same sorting indices
        phi_s_sorted = phi_s(sortIdx);
        phi_s = phi_s_sorted;
    end

    % Misc. Other Calculations before while loop begins
    bw1 = directivity_met_v2(phi, F_total, phi_0);
    directivity_metric_1_beamwidth_store(1) = bw1.beamwidth;
    
    if isempty(Slobe)
        % No sidelobes above threshold — store LOW dummy values
        %max_sidelobe_store(iter+1) = -Inf;
        %max_sidelobe_store(iter) = NaN;
        %max_side_phi_store(iter) = NaN;
        max_sidelobe_store(1) = NaN;
        max_side_phi_store(1) = NaN;            
    else
        % Slobe is already sorted largest → smallest
        %max_sidelobe_store(iter) = Slobe(1);
        %max_side_phi_store(iter) = phi_s(1);
        max_sidelobe_store(1) = Slobe(1);
        max_side_phi_store(1) = phi_s(1);
    end


    %% Step 7: Number of remaining sidelobes
    if isempty(Slobe)
        m = 0; %Number of remaining sidelobes if empty
    else
        m = numel(Slobe);
    end

    initial_m = m; % record the number of sidelobes in the initial pattern

    if verbose
        % Debug printout
        fprintf('Found %d initial sidelobes above %.1f dB.\n', m, eps_dB);
    end
        % Optional initial plot
    if (show_plots || show_plots_st7)
        lab_3 = "Pattern immediatly prior to (first) While Loop (Step 7)";
        %lab_3 = "Plot of Initial Pattern";
        % View function graph
        plot_pattern_v5(phi, F_total, ...
            'label',lab_3, ...
            'phi_0', phi_0, ...
            'phi_s', phi_s, ...
            'Slobe', Slobe, ...
            'show_plots', true, ...
            'Big_phi', main_peakLoc_store(1) );
    end


    %% ---- Steps 8-16 ----
    
    %% Step 8: Begin While Loop for evaluating peaks above eps_dB
    while (m > 0 && iter <= Max_iter)
        if verbose 
            disp(['iter = ' num2str(iter)]); %debugging output
        end
 
        % Optional per-epoch plot (taken at start of epoch)
        if show_plots
            lab_4 = "Pattern immediatly prior to For Loop(Step 8)";
            % View function graph
            plot_pattern_v5(phi, F_total, ...
                'label',lab_4, ...
                'phi_0', phi_0, ...
                'null_phi', null_phi, ...
                'phi_s', phi_s, ...
                'Slobe', Slobe, ...
                'iter', iter, ...
                'show_plots', true );
        end


    %% Step 9: For-Loop to deal with m sidelobes
        if full_loop %set whether full- or single-type loop
            m_epoch = m; % for adjusting all sidelobes in one pass
        else
            m_epoch = 1; % for adjusting one sidelobe at a time
            % Note: provided the phi_s are ordered latgest to smallest, 
            % thise should tell the algorythm to use the largest only.
        end

        for t = 1:m_epoch % Begin the sidelobe-adjustment loop
           %% Step 10: delta_corr = beamfocusing(phi_S, x, y, k0)
            % AKA: Construct correction aiming at worst_phi
            delta_corr = -k0 * ( x*cos(phi_s(t)) + y*sin(phi_s(t)) );
            % Note: For the fist pass on the while-loop, phi_s is given by
            % previous part of code. For subsequent passes, it is given 
            % further by later part of algorythm in previous step.

            %% Step 11: Compute correction amplitude
            % AKA: Calculate current field at given (worst) sidelobe
            % Interpolate the complex array factor at the sidelobe direction φs(j)
            % Note: You do an interpolation since you need to pick a single result
            % from the grid of M \phi values, and because you might not be
            % dealling with an exact member of your phi-mesh.
            F_at_phi_s = interp1(phi, F_total, phi_s(t), 'linear', 'extrap');
            % Compute per-element complex amplitude
            %A_corr = -F_at_phi_s / N;
            if use_null
                % Use only outer elements for corrections
                Ncorr = numel(outer_idx);
                A_corr_scalar = -F_at_phi_s / Ncorr;
    
                A_corr_vec = zeros(N,1);
                A_corr_vec(outer_idx) = A_corr_scalar;
            else
                % Use all elements (no-Null case)
                A_corr_scalar = -F_at_phi_s / N;
                A_corr_vec = A_corr_scalar * ones(N,1);
            end

            
            %% Step 12: Calculate and Add correction pattern
            % Add correction term
            F_add = F2d(phi, A_corr_vec, x, y, delta_corr, k0);
            F_total = F_total + F_add;
            
            % Optional storage
            if (return_funcs)
                %F_store(iter+1) = F_total; % record iterate pattern
                F_store(iter+1, :) = F_total(:).'; % record iterate pattern
            end            


            % --- Save correction info ---
            A_store{end+1}     = A_corr_vec;
            delta_store{end+1} = delta_corr;
            phi_store(end+1)   = phi_s(t);

            % Calculate Effective Overall Amplitudes
            % Recompose As for non-null case
            if ~use_null
            %    for k = 1:length(A_store)
            %        A_eff_store{end+1} = A_eff_store{end} + A_store{k} .* exp(1j * delta_store{k});
            %    end
            A_eff_store{end+1} = A_eff_store{end} + ...
            A_corr_vec .* exp(1j * delta_corr);
            end

            G2D_store(iter+1) = gain_calc(F_total, phi, phi_0);
            G3D_store(iter+1) = gain_calc_3D( ...
            F3D(phi, theta_mesh, A_eff_store{end}, x, y, z, [], k0), ...
            phi, theta_mesh, phi_0, theta_0);

            % Optional Correction Pattern plot (Needs modification to include for loop iteration)
            if show_plots
                %lab_5 = "Plot of Correction Pattern (within For Loop)(Step 12)";
                lab_5 = "Plot of Correction Pattern (within For Loop)(Step 12: 'f_{cor}')";
                % View function graph
                plot_pattern_v5(phi, F_add, ...
                    'label',lab_5, ...
                    'phi_0', phi_s(t), ...
                    'iter', iter, ...
                    'show_plots', true );
            end




            

        end

        
        iter = iter + 1; % increase iteration for the while loop



        if (use_null == false)&&(show_plots || show_plots_st12) %for no-null case
        % Optional Pattern plot (after For LoopNeeds modification to include for loop iteration)
            %lab_6 = "Plot of Pattern (Step 12)(test)";
            %lab_6 = "Plot of Corrected Pattern";
            lab_6 = "Plot of Corrected Pattern (Step 12: 'f_{new}')";
            % View function graph
            plot_pattern_v5(phi, F_total, ...
                'label',lab_6, ...
                'phi_0', phi_0, ...
                'iter', iter, ...
                'show_plots', true );
        end


        %% Step 12N: Optional null synthesis (using center element only)
        % Here is code for the method of updating the null every epoch of
        % the While Loop
        if (use_null && const_null_update)
            % Step 12N17: Compute delta_null (phase steering for null direction)
            % Apply the same beamfocusing rule, but only for the central element
            delta_null = -k0 * (x(center_idx)*cos(null_phi) + y(center_idx)*sin(null_phi));
            
            % Step 12N18: Measure the array response at phi_N and compute null amplitude
            F_at_phi_N = interp1(phi, F_total, null_phi, 'linear', 'extrap');  % complex value at null direction
            A_null = -F_at_phi_N;  % amplitude that cancels this field
            
            % Step 12N19: Build and add null-generating pattern
            A_null_vec = zeros(N,1);
            A_null_vec(center_idx) = A_null;
            
            delta_null_vec = zeros(N,1);
            delta_null_vec(center_idx) = delta_null;
            
            F_null = F2d(phi, A_null_vec, x, y, delta_null_vec, k0);
            F_total = F_total + F_null;

            % --- Save correction info ---
            A_store{end+1}     = A_null_vec;
            delta_store{end+1} = delta_null_vec;
            
            % Calculate Effective Overall Amplitudes
            % Recompose As for non-null case
            if use_null
            %    for k = 1:length(A_store)
            %        A_eff_store{end+1} = A_eff_store{end} + A_store{k} .* exp(1j * delta_store{k});
            %    end
            A_eff_store{end+1} = A_eff_store{end} + ...
            A_null_vec .* exp(1j * delta_null_vec);
            end

            G2D_store(iter+1) = gain_calc(F_total, phi, phi_0);
            G3D_store(iter+1) = gain_calc_3D( ...
            F3D(phi, theta_mesh, A_eff_store{end}, x, y, z, [], k0), ...
            phi, theta_mesh, phi_0, theta_0);
        
            if show_plots
                figure;
            
                % Compute and clip normalized pattern
                Fdb_iter = 10*log10(abs(F_total).^2 / max(abs(F_total).^2));
                Fdb_iter(Fdb_iter < -40) = -40;   % hard clip below -40 dB
            
                % Plot array factor
                hPat = polarplot(phi, Fdb_iter, 'b'); 
                hold on;
                rlim([-40 0]);
            
                % Focus direction (green)
                rline = rlim;
                hFocus = polarplot([phi_0 phi_0], rline, 'g', 'LineWidth', 2);
            
                % Sidelobe direction lines (red)
                if ~isempty(phi_s)
                    rmin = rline(1);
                    hSideLine = gobjects(length(phi_s), 1);  % preallocate handles
                    % --- make ONE representative sidelobe line for legend ---
                    hSideLineLegend = polarplot([phi_s(1) phi_s(1)], [rmin Slobe(1)], ...
                                     'r', 'LineWidth', 1.5);
                    for k = 1:length(phi_s)
                        hSideLine(k) = polarplot([phi_s(k) phi_s(k)], [rmin Slobe(k)], ...
                                                  'r', 'LineWidth', 1.5);
                    end
                        
                    % Sidelobe peaks (red dots)
                    hSideDot = polarplot(phi_s, Slobe, 'ro', 'MarkerFaceColor','r');
                end            
                % Sidelobe peaks (red dots)
                hSideDot = polarplot(phi_s, Slobe, 'ro', 'MarkerFaceColor','r');
            
                % Title
                %title(sprintf('Plot With Null (Const Update method)'));
                title(sprintf('Epoch %d: Plot With Null (Const Update method)',iter+1));
                %fprintf('Iteration %d: no peaks found; stopping.\n', iter);
    
                % Legend
                if use_null % Null direction (black)
                    hNull = polarplot([null_phi null_phi], rline, 'k', 'LineWidth', 2);
                    legend([hPat, hFocus, hSideLineLegend, hNull], ...
                           {'Pattern', 'Focus', 'Sidelobe', 'Null'}, ...
                           'Location', 'bestoutside');
                else
                    legend([hPat, hFocus, hSideLine], ...
                           {'Pattern', 'Focus', 'Sidelobe'}, ...
                           'Location', 'bestoutside');
                end            
                %{
                 % Legend — use representative handles only
                legend([hPat, hFocus, hSideLineLegend], {'Pattern', 'Focus', 'Sidelobe'}, ...
                       'Location', 'bestoutside');
                %}
                hold off;
                drawnow;
            end        
        end

        %% Step 13: Find all local maxima (peaks) in the updated pattern
        Fmag = abs(F_total);
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
        if isempty(peakVals) % error handeling
            if verbose
                fprintf('Iteration %d: no peaks found; stopping.\n', iter);
            end
        end        

        %% Step 14: Identifying which of the lobes is the largest (the focus). 
        %[~, mainIdx] = min(abs(peakLocs - phi_0)); %old method
        [~, mainIdx] = min(ang_diff(peakLocs, phi_0));
        
        %% Step 15: Keep only peaks above the sidelobe threshold eps_dB
        % Step 15: Identify and keep only sidelobes with peaks above the specified
        % threshold (-20db)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        % Record the main beam for future analysis
%{
        main_peakLoc_store(iter) = peakLocs(mainIdx);
        main_peakVal_store(iter) = peakVals(mainIdx);
        %main_peak_skew(iter+1) = (phi_0-main_peakLoc_store(iter+1)); %original
        main_peak_skew(iter) = atan2(sin(phi_0 - main_peakLoc_store(iter)), cos(phi_0 - main_peakLoc_store(iter)));
        % Record value at focus angle  for future analysis
        focus_value_store(iter) = interp1(phi, F_total, phi_0, 'linear', 'extrap');        
%}
        main_peakLoc_store(iter+1) = peakLocs(mainIdx);
        main_peakVal_store(iter+1) = peakVals(mainIdx);
        %main_peak_skew(iter+1) = (phi_0-main_peakLoc_store(iter+1)); %original
        main_peak_skew(iter+1) = atan2(sin(phi_0 - main_peakLoc_store(iter)), cos(phi_0 - main_peakLoc_store(iter)));
        % Record value at focus angle  for future analysis
        focus_value_store(iter+1) = interp1(phi, F_total, phi_0, 'linear', 'extrap');   
        focus_value_store_dB(iter+1) = 10*log10( ...
            (interp1(phi, F_total, phi_0, 'linear', 'extrap').^2) / (max(Fmag).^2));
        % Remove the main beam from the list
        peakVals(mainIdx) = [];
        peakLocs(mainIdx)    = [];
    
        if isempty(peakVals) % if there are no other sidelobes
            if verbose
                fprintf('Iteration %d: no sidelobes; stopping.\n', iter);
            end
            Slobe = [];
            phi_s = [];
        elseif (~isempty(peakVals) && ~isempty(cone_rad)) % if there are designated conebounds
            peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
            validMask_db = peakVals_db > eps_dB;
            % TEST CODE FOR CONE EXCLUSION
            % Smallest signed angle difference in (-pi, pi]
            d = mod(peakLocs - phi_0 + pi, 2*pi) - pi;
            % Logical mask: 1 (true) if outside cone_rad, else 0 (false)
            validMask_cone = abs(d) > cone_rad;   % logical array, same size as peakLocs
            %validMask_cone = %Code for identifying peaks inside cone bounds from focus phi_0
            
            validMask = validMask_cone & validMask_db;
            Slobe = peakVals_db(validMask);
            phi_s = peakLocs(validMask);
            % Sort sidelobes from largest to smallest
            [Slobe_sorted, sortIdx] = sort(Slobe, 'descend');
            Slobe = Slobe_sorted;
            % Reorder angles using the same sorting indices
            phi_s_sorted = phi_s(sortIdx);
            phi_s = phi_s_sorted; 
        else
            peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
            validMask = peakVals_db > eps_dB;
            Slobe = peakVals_db(validMask);
            phi_s = peakLocs(validMask);
            % Sort sidelobes from largest to smallest
            [Slobe_sorted, sortIdx] = sort(Slobe, 'descend');
            Slobe = Slobe_sorted;
            % Reorder angles using the same sorting indices
            phi_s_sorted = phi_s(sortIdx);
            phi_s = phi_s_sorted;
        end

        %% Step 16: Update number of sidelobes remaining
        m = numel(Slobe);
        
        if verbose
        % Debugg: diagnostic output and plot
        fprintf('After Iteration %d: %d sidelobes above %.1f dB\n', iter, m, eps_dB);
        end
        
        % Optional Pattern plot (after For LoopNeeds modification to include for loop iteration)
        if (show_plots || show_plots_st16)
            %lab_7 = "Plot (Step 16)(test)";
            lab_7 = "Plot of Corrected Pattern (Step 16: 'f_{new}')";
            % View function graph
            plot_pattern_v5(phi, F_total, ...
                'label',lab_7, ...
                'phi_0', phi_0, ...
                'phi_s', phi_s, ...
                'Slobe', Slobe, ...
                'null_phi', null_phi , ...
                'iter', iter, ...
                'show_plots', true, ...
                'Big_phi', main_peakLoc_store(iter));
        end        
        
        % Misc. Code At End Of While Loop
        bw = directivity_met_v2(phi, F_total, phi_0);
%        directivity_metric_1_beamwidth_store(iter) = bw.beamwidth;
         directivity_metric_1_beamwidth_store(iter+1) = bw.beamwidth;
        % ---- Store the max sidelobe and its angle for this epoch ----
        if isempty(Slobe)
            % No sidelobes above threshold — store LOW dummy values
            %max_sidelobe_store(iter+1) = -Inf;
            %max_sidelobe_store(iter) = NaN;
            %max_side_phi_store(iter) = NaN;
            max_sidelobe_store(iter+1) = NaN;
            max_side_phi_store(iter+1) = NaN;            
        else
            % Slobe is already sorted largest → smallest
            %max_sidelobe_store(iter) = Slobe(1);
            %max_side_phi_store(iter) = phi_s(1);
            max_sidelobe_store(iter+1) = Slobe(1);
            max_side_phi_store(iter+1) = phi_s(1);
        end
        %iter = iter + 1; % increase iteration for the while loop

    end  % End of while loop
    
    %% ---- Final Calculations ----
    % Find all local maxima (peaks) in the final pattern
        Fmag = abs(F_total);
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);    
    % Identifying which of the lobes is the largest (the focus). 
        %[~, mainIdx] = min(abs(peakLocs - phi_0)); %old method
        [~, mainIdx] = min(ang_diff(peakLocs, phi_0));
    % Keep only peaks above the sidelobe threshold eps_dB
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        % Record then remove the main beam from the list
        Big_Val_final = peakVals(mainIdx);
        Big_phi_final = peakLocs(mainIdx);
        peakVals(mainIdx) = [];
        peakLocs(mainIdx)    = [];
        
        if isempty(peakVals)
            Slobe_fin = [];
            phi_s_fin = [];
            phi_s_sorted_fin = [];
        else
            peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
            Slobe_fin = peakVals_db;
            phi_s_fin = peakLocs;
            % Sort sidelobes from largest to smallest
            [Slobe_sorted, sortIdx] = sort(Slobe_fin, 'descend');
            Slobe_fin = Slobe_sorted;
            % Reorder angles using the same sorting indices
            phi_s_sorted_fin = phi_s_fin(sortIdx);
            phi_s_fin = phi_s_sorted_fin;
        end
    % Record Final value at focus angle
        F_at_phi_0 = interp1(phi, F_total, phi_0, 'linear', 'extrap');

    %% Final Plots
    if (~use_null) %1-Beam-0-Null
        % Final plot
        if (show_plots) || (show_final_plot)
            lab_10 = "Final Plot: 1-Beam-0-Null Method";
            % View function graph
            plot_pattern_v5(phi, F_total, ...
                'label',lab_10, ...
                'phi_0', phi_0, ...
                'phi_s', phi_s, ...
                'Slobe', Slobe, ...
                'null_phi', null_phi , ...
                'iter', iter, ...
                'show_plots', true, ...
                'cone_rad', cone_rad, ...
                'Big_phi', Big_phi_final);
        end
    end

    if (use_null && const_null_update) %1-Beam-1-Null-constant-update
        % Final plot
        if (show_plots) || (show_final_plot)
            lab_10 = "Final Plot: 1-Beam-1-Null (Const. update) Method";
            % View function graph
            plot_pattern_v5(phi, F_total, ...
                'label',lab_10, ...
                'phi_0', phi_0, ...
                'phi_s', phi_s, ...
                'Slobe', Slobe, ...
                'null_phi', null_phi , ...
                'iter', iter-1, ...
                'show_plots', true, ...
                'cone_rad', cone_rad, ...
                'Big_phi', Big_phi_final);
        end
    end    

    %% ---- Steps 17-19: Optional null synthesis (using center element only) ----
    if (use_null && ~const_null_update)
        %% Step 17: Compute delta_null (phase steering for null direction)
        % Apply the same beamfocusing rule, but only for the central element
        delta_null = -k0 * (x(center_idx)*cos(null_phi) + y(center_idx)*sin(null_phi));
        
        %% Step 18: Measure the array response at phi_N and compute null amplitude
        F_at_phi_N = interp1(phi, F_total, null_phi, 'linear', 'extrap');  % complex value at null direction
        A_null = -F_at_phi_N;  % amplitude that cancels this field
        
        %% Step 19: Build and add null-generating pattern
        A_null_vec = zeros(N,1);
        A_null_vec(center_idx) = A_null;
        
        delta_null_vec = zeros(N,1);
        delta_null_vec(center_idx) = delta_null;
        
        F_null = F2d(phi, A_null_vec, x, y, delta_null_vec, k0);
        F_total = F_total + F_null;
        
    % Find all local maxima (peaks) in the final pattern
        Fmag = abs(F_total);
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);    
    % Identifying which of the lobes is the largest (the focus). 
        %[~, mainIdx] = min(abs(peakLocs - phi_0)); %old method
        [~, mainIdx] = min(ang_diff(peakLocs, phi_0));
    % Keep only peaks above the sidelobe threshold eps_dB
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        % Record then remove the main beam from the list
        Big_Val_final = peakVals(mainIdx);
        Big_phi_final = peakLocs(mainIdx);
        peakVals(mainIdx) = [];
        peakLocs(mainIdx)    = [];
    
        if isempty(peakVals)
            Slobe_fin = [];
            phi_s_fin = [];
            phi_s_sorted_fin = [];
        else
            peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
            Slobe_fin = peakVals_db;
            phi_s_fin = peakLocs;
            % Sort sidelobes from largest to smallest
            [Slobe_sorted, sortIdx] = sort(Slobe, 'descend');
            Slobe_fin = Slobe_sorted;
            % Reorder angles using the same sorting indices
            phi_s_sorted_fin = phi_s(sortIdx);
            phi_s_fin = phi_s_sorted;
        end

        % Final plot
        if (show_plots || show_final_plot) 
            %lab_8 = "Final Plot With Null (simple method)(Step 19)";
            lab_8 = "Final Plot: 1-Beam-1-Null (Basic Method)(Step 19)";
            % View function graph
            plot_pattern_v5(phi, F_total, ...
                'label',lab_8, ...
                'phi_0', phi_0, ...
                'phi_s', phi_s, ...
                'Slobe', Slobe, ...
                'null_phi', null_phi , ...
                'iter', iter+1, ...
                'show_plots', true, ...
                'cone_rad', cone_rad, ...
                'Big_phi', Big_phi_final);
        end

    end

    %% ---- Calculate Effective Overall Amplitudes ----
    A_eff = zeros(size(A_store{1}));
    
    % Recompose As for non-null case
    if ~use_null
        for k = 1:length(A_store)
            A_eff = A_eff + A_store{k} .* exp(1j * delta_store{k});
        end
    end
    
    delta_eff = zeros(size(A_eff)); % already absorbed
    
    % Do this to recompose function:
    % F_eff = F2d(phi, A_eff, x, y, delta_eff, k0);
    % Do this to double check:
    % max(abs(F_eff - results1.final_function))   % should be very small

    % Test and Debug Code
    %F_3D = F3D(phi, theta_mesh, A_eff, x, y, z, [], k0)
    %gain_calc_3D(F_3D, phi, theta_mesh, phi_0, theta_0)
    %F_eff_2D = F2d(phi, A_eff, x, y, zeros(size(A_eff)), k0);
    %max(abs(F_eff_2D - F_total))

    %% ---- Results ----
    final_epoch = iter;
    total_time = toc;
    % ---- Outputs ----
    results.final_epoch = final_epoch;
    results.final_iteration = iter;
    results.total_time  = total_time;
    results.m = m;
    results.focus_angle = phi_0;
    results.focus_angle_deg = round(rad2deg(phi_0));
    results.cone_rad = cone_rad;
    if use_null
        results.null_angle = null_phi;
        results.null_angle_deg = round(rad2deg(null_phi));
    else
        results.null_angle = [];
        results.null_angle_deg = [];
    end
        % Optional storage
    if (return_funcs)
        results.F_store = F_store;
        %results.F3D_store = F_3D;
    end
    results.max_sidelobe_store = max_sidelobe_store;
    results.max_side_phi_store = max_side_phi_store;
    results.main_peakLoc_store = main_peakLoc_store;
    results.main_peakVal_store = main_peakVal_store;
    results.main_peak_skew = main_peak_skew;
    results.directivity_metric_1_beamwidth_store = directivity_metric_1_beamwidth_store;
    results.final_function = F_total;
    results.phi_s_sorted_fin = phi_s_sorted_fin;
    results.phi_s_fin = phi_s_fin;
    results.Big_Val_final = Big_Val_final;
    results.Big_phi_final = Big_phi_final;
    results.F_at_phi_0 = sqrt(F_at_phi_0.^2); % without imaginary component
    %results.F_at_phi_0 = abs(F_at_phi_0); % without imaginary component
    %results.F_at_phi_0 = F_at_phi_0; % with imaginary component
    %results.focus_value_store = focus_value_store; % with imaginary component
    results.focus_value_store = abs(focus_value_store); % without imaginary component
    results.focus_value_store_dB = abs(focus_value_store_dB); % without imaginary component
    results.A_store = A_store;
    results.A_eff_store = A_eff_store;
    results.delta_store = delta_store;
    results.phi_store = phi_store;
    results.A_eff = A_eff;
    results.delta_eff = delta_eff;
    results.x_pos = x;
    results.y_pos = y;
    results.initial_m = initial_m;
    results.final_gain2D = gain_calc(F_total, phi, phi_0);
    %results.final_gain3D = gain_calc_3D(F_3D, phi, theta_mesh, phi_0, theta_0);
    results.final_gain3D = gain_calc_3D(F3D(phi, theta_mesh, A_eff, x, y, z, [], k0), ...
        phi, theta_mesh, phi_0, theta_0);
    results.G2D_store = G2D_store;
    results.G3D_store = G3D_store;

end