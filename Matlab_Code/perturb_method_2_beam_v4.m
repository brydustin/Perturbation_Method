%% Perturbative Method Code (Special 2-Beam Version)
% Version 4:
% Contains code for beam-focussing with two focuses.
% based on the simple version of the 2-Beam method from Dr. Onofreis paper
% 12/11/2025
% Dependencies: Uses d1d2Convert.m, plot_pattern_v3.m, directivity_met_v2.m
%
% Version Update: Initial version
%
function results = perturb_method_2_beam_v4(varargin)
% -------------------------------------------------------------------------
%   Two-Beam Closed-Form Array Factor Generator
%
%   AF(phi) = A0 + sum_{n=1}^{N-1} A_n * exp(j k0 (x_n cos(phi) + y_n sin(phi)))
%
%   where:
%       A_n = exp(-j k0 r_n · phi01) + exp(-j k0 r_n · phi02)
%
%       A_0 = -sum exp(-j k0 r_n·phi01) exp(+j k0 r_n·phi02)
%             -sum exp(-j k0 r_n·phi02) exp(+j k0 r_n·phi01)
%
%   Produces two main beams at phi_0_1 and phi_0_2.
% -------------------------------------------------------------------------
% Outputs:
%   results.total_time
%   results.focus_angle_1
%   results.focus_angle_2
%   results.max_sidelobe_store
%   results.max_side_phi_store
%   results.directivity_metric_1_beamwidth_store_1
%   results.directivity_metric_1_beamwidth_store_2
%   results.final_function
%   results.final_epoch

% Too Do List:

    %% ---- Handle input arguments ----
    p = inputParser;
    p.FunctionName = 'perturb_method_2_beam_v4';

    % Required inputs
    addRequired(p, 'x',        @isnumeric); % vector of x coordinates
    addRequired(p, 'y',        @isnumeric); % vector of y coordinates
    addRequired(p, 'phi_0_1',  @isnumeric); % first focus direction (in radians)
    addRequired(p, 'phi_0_2',  @isnumeric); % second focus direction (in radians)

    % Optional inputs (name–value pairs; make sure to use "addParameter")
    addParameter(p, 'Max_iter',         40, @isnumeric);
    addParameter(p, 'eps_dB',           -20, @isnumeric);    
    addParameter(p, 'verbose',          false, @islogical);
    addParameter(p, 'show_plots',       false, @islogical);
    addParameter(p, 'show_plot_raw',    false, @islogical);
    addParameter(p, 'show_plot_init',   false, @islogical);
    addParameter(p, 'show_plots_st7',   false, @islogical);
    addParameter(p, 'show_plots_st12',  false, @islogical);
    addParameter(p, 'show_final_plot',  false, @islogical);
    addParameter(p, 'full_loop',        false, @islogical); %for whether to loop over all sidelobes
    addParameter(p, 'null_phi',            [], @isnumeric); % currently unused. exists for legacy code
    addParameter(p, 'cone_rad',            [], @isnumeric);   % for cone boundaries
    addOptional(p, 'return_funcs',      false, @islogical);
    addOptional(p, 'theta_0',             pi.*0.5, @isnumeric);
    addOptional(p, 'z',                    [], @isnumeric);
    addOptional(p, 'A_init',               [], @isnumeric);
    addOptional(p, 'show_plots_st16',   false, @islogical);

    % ----- Parse everything -----
    parse(p, varargin{:});
    args = p.Results;

    % Extract into local variables
    x               = args.x(:);
    y               = args.y(:);
    z               = args.z(:);
    phi_0_1         = args.phi_0_1;
    phi_0_2         = args.phi_0_2;
    cone_rad        = args.cone_rad;
    Max_iter        = args.Max_iter;
    eps_dB          = args.eps_dB;    

    verbose         = args.verbose;
    show_plots      = args.show_plots;
    show_plot_raw   = args.show_plot_raw;
    show_plot_init  = args.show_plot_init;
    show_plots_st7  = args.show_plots_st7;
    show_plots_st12 = args.show_plots_st12;
    show_plots_st16 = args.show_plots_st16;
    show_final_plot = args.show_final_plot;
    full_loop       = args.full_loop;
    null_phi        = args.null_phi;  
    A_init          = args.A_init;
    return_funcs      = args.return_funcs;    
    theta_0           = args.theta_0;
    


    %% ---- Modify Input Angles to conform to Polar Space ----
    phi_0_1 = mod(phi_0_1, 2*pi);
    phi_0_2 = mod(phi_0_2, 2*pi);
    theta_0 = mod(theta_0, 2*pi);
    null_phi = mod(null_phi, 2*pi);

    %% ---- Initialize Special Script Variables
%    outdir = 'D:\Research\Dr. Onofreis projects\DS MATLAB CODE\Github_Shared_Code\Relay-Phased-Array-Optimization-main\Plot_Saves';
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
    center_idx = 1;     % reserve element 1 for special use w.r.t. null
    outer_idx  = setdiff(1:N, center_idx);

    % Evaluation grid (for computing the pattern)
    mesh_len = 1000; % length of phi-mesh for plotting pattern
    %phi = linspace(0, 2*pi, 1000); %original
    % Deliberatly remove 2pi endpoint
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
        %E = where(abs(sin(TH)) < 1e-8, 0, E);

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
        %G = 10*log10((F_at_phi_0.^2 * 4*pi)./I);
        G = 10*log10((abs(F_at_phi_0).^2 * 4*pi)./I);
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
        %F0 = interp2(phi_mesh, theta_mesh, F_total, phi_0, theta_0, 'linear');
        F0 = interp2(phi_mesh, theta_mesh, F_total, phi_0, theta_0, 'linear', 0);

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

    %% ---- Begin the Algorythm ---- 
    
    % Preliminary: 
    tic; % Start computation timer
    iter = 0; % Initialize iteration counter

   

    %% ---- Pre-allocate storage for various calculated value and max sidelobe tracking ----
    max_sidelobe_store = nan(Max_iter,1); % for max sidelobe value
    max_side_phi_store = nan(Max_iter,1); % for max sidelobe direction
    main_peakLoc_store_1 = nan(Max_iter,1); % for main peak direction
    main_peakVal_store_1 = nan(Max_iter,1); % for main peak value
    focus_value_store_1 = nan(Max_iter,1); % for value in focus direction
    main_peakLoc_store_2 = nan(Max_iter,1); % for main peak direction
    main_peakVal_store_2 = nan(Max_iter,1); % for main peak value
    focus_value_store_2 = nan(Max_iter,1); % for value in focus direction    
    directivity_metric_1_beamwidth_store_1 = nan(Max_iter,1); % for directivity metric_1
    directivity_metric_1_beamwidth_store_2 = nan(Max_iter,1); % for directivity metric_2
    main_peak_skew_1 = nan(Max_iter,1); % for deviation betweem the main peak angle and focus direction
    main_peak_skew_2 = nan(Max_iter,1); % for deviation betweem the main peak angle and focus direction
    % Record Final value at focus angle
    %    focus_value_store(1) = interp1(phi, F_total, phi_0, 'linear', 'extrap');

    %% ---- Compute steering phase terms ----
    phase_01 = -k0 * (x*cos(phi_0_1) + y*sin(phi_0_1));   % steering to focus 1
    phase_02 = -k0 * (x*cos(phi_0_2) + y*sin(phi_0_2));   % steering to focus 2

    %%  ---- Steps 1-3 ----
    % The Following substitute steps 1-3 from the normal 1-beam method:
        
    %% ---- Compute A_n for n = 1..N-1 (outer elements) ----
    A_n = exp(-1j*phase_01) + exp(-1j*phase_02);  % Nx1 complex

    %% ---- Compute A_0 (special element) ----
    term1 = exp(-1j*phase_01) .* exp(+1j*phase_02);
    term2 = exp(-1j*phase_02) .* exp(+1j*phase_01);
    
    A_0 = -(sum(term1(2:end)) + sum(term2(2:end)));
    
    %% ---- Compute full array factor AF(phi) ----
    % Phase matrix for outer elements: (N-1) x M
    phi_grid = phi(:).';
    phase_grid = k0*(x(2:end)*cos(phi_grid) + y(2:end)*sin(phi_grid));
    
    % AF = A0 + sum A_n e^{j phase}
    AF = A_0 + sum( A_n(2:end).*exp(1j*phase_grid), 1 );

    % Optional initial plot
    if (show_plots || show_plot_init)
        lab_2 = "Initial Pattern (with Analytic Focuses)(Step 3)";
        % View function graph
        plot_pattern_v4(phi, AF, 'label',lab_2, 'phi_0', [phi_0_1 phi_0_2], 'show_plots', true );
    end    


    %% ---- Steps 4-7 ----
    %% Step 4: Identify all the local maxima for the function (thus all lobes including the focus)
    F_total = AF;
    Fmag = abs(F_total);
    [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
    if isempty(peakVals) % error handeling
        if verbose
            fprintf('Iteration %d: no peaks found; stopping.\n', iter);
        end
    end
    %peakLocs = mod(peakLocs, 2*pi);

    %% Step 5: Identifying which of the lobes are the 2 largest (the foci). 
    % Identifying which of the lobes corresponds to phi_0_1 (the first focus). 
        [~, first_mainIdx] = min(abs(peakLocs - phi_0_1));    
    % Record and remove the peak corresponds to phi_0_1 (the first focus)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        Big_Val_1 = peakVals(first_mainIdx);
        Big_phi_1 = peakLocs(first_mainIdx);
        peakVals(first_mainIdx) = [];
        peakLocs(first_mainIdx)    = [];
    % Identifying which of the lobes corresponds to phi_0_2 (the second focus). 
        [~, second_mainIdx] = min(abs(peakLocs - phi_0_2));    
    % Record and remove the peak corresponds to phi_0_1 (the first focus)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        Big_Val_2 = peakVals(second_mainIdx);
        Big_phi_2 = peakLocs(second_mainIdx);
        peakVals(second_mainIdx) = [];
        peakLocs(second_mainIdx)    = [];

    %% Step 6: Identify and keep only sidelobes with peaks above the specified
    % Record the main beam for future analysis
    main_peakLoc_store_1(1) = Big_phi_1;
    main_peakVal_store_1(1) = Big_Val_1;
    main_peakLoc_store_2(1) = Big_phi_2;
    main_peakVal_store_2(1) = Big_Val_2;
    % Record main beam skews
    main_peak_skew_1(1) = (phi_0_1-main_peakLoc_store_1(1));
    main_peak_skew_2(1) = (phi_0_2-main_peakLoc_store_2(1));
    % Record values at focus angles for future analysis
    focus_value_store_1(1) = interp1(phi, F_total, phi_0_1, 'linear', 'extrap');
    focus_value_store_2(1) = interp1(phi, F_total, phi_0_2, 'linear', 'extrap');

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
        d_1 = mod(peakLocs - phi_0_1 + pi, 2*pi) - pi;
        d_2 = mod(peakLocs - phi_0_2 + pi, 2*pi) - pi;
        % Logical mask: 1 (true) if outside cone_rad, else 0 (false)
        validMask_cone_1 = abs(d_1) > cone_rad;   % logical array, same size as peakLocs
        validMask_cone_2 = abs(d_2) > cone_rad;   % logical array, same size as peakLocs
        %validMask_cone = %Code for identifying peaks inside cone bounds from focus phi_0
        validMask_cone = validMask_cone_1 & validMask_cone_2;

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

    %% Step 7: Number of remaining sidelobes
    if isempty(Slobe)
        m = 0; %Number of remaining sidelobes if empty
    else
        m = numel(Slobe);
    end

    if verbose
        % Debug printout
        fprintf('Found %d initial sidelobes above %.1f dB.\n', m, eps_dB);
    end
        % Optional initial plot
    if (show_plots || show_plots_st7)
        lab_3 = "Pattern immediatly prior to (first) While Loop (Step 7)";
        %lab_3 = "Plot of Initial Pattern";
        % View function graph
        plot_pattern_v3(phi, F_total, 'label',lab_3, 'phi_0', phi_0, 'phi_s', phi_s, 'Slobe', Slobe, 'show_plots', true );
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
            plot_pattern_v3(phi, F_total, 'label',lab_4, 'phi_0', phi_0, 'null_phi', null_phi, 'phi_s', phi_s, 'Slobe', Slobe, 'iter', iter, 'show_plots', true );
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

            % Optional Correction Pattern plot (Needs modification to include for loop iteration)
            if show_plots
                %lab_5 = "Plot of Correction Pattern (within For Loop)(Step 12)";
                lab_5 = "Plot of Correction Pattern (within For Loop)(Step 12: 'f_{cor}')";
                % View function graph
                plot_pattern_v3(phi, F_add, 'label',lab_5, 'phi_0', phi_s(t), 'iter', iter, 'show_plots', true );
            end
        end 
        if (show_plots || show_plots_st12) %for no-null case
        % Optional Pattern plot (after For LoopNeeds modification to include for loop iteration)
            %lab_6 = "Plot of Pattern (Step 12)(test)";
            %lab_6 = "Plot of Corrected Pattern";
            lab_6 = "Plot of Corrected Pattern (Step 12: 'f_{new}')";
            % View function graph
            plot_pattern_v3(phi, F_total, 'label',lab_6, 'phi_0', phi_0, 'iter', iter, 'show_plots', true );
        end

        %% Step 13: Find all local maxima (peaks) in the updated pattern
        Fmag = abs(F_total);
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);
        if isempty(peakVals) % error handeling
            if verbose
                fprintf('Iteration %d: no peaks found; stopping.\n', iter);
            end
        end  

        %% Step 14: Identifying which of the lobes are the 2 largest (the foci). 
        % Identifying which of the lobes corresponds to phi_0_1 (the first focus). 
        [~, first_mainIdx] = min(abs(peakLocs - phi_0_1));    
        % Record and remove the peak corresponds to phi_0_1 (the first focus)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        Big_Val_1 = peakVals(first_mainIdx);
        Big_phi_1 = peakLocs(first_mainIdx);
        peakVals(first_mainIdx) = [];
        peakLocs(first_mainIdx)    = [];
        % Identifying which of the lobes corresponds to phi_0_2 (the second focus). 
        [~, second_mainIdx] = min(abs(peakLocs - phi_0_2));    
        % Record and remove the peak corresponds to phi_0_1 (the first focus)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        Big_Val_2 = peakVals(second_mainIdx);
        Big_phi_2 = peakLocs(second_mainIdx);
        peakVals(second_mainIdx) = [];
        peakLocs(second_mainIdx)    = [];
    
        %% Step 15: Keep only peaks above the sidelobe threshold eps_dB
        % Step 15: Identify and keep only sidelobes with peaks above the specified
        % threshold (-20db)
        % Record the main beams for future analysis
        main_peakLoc_store_1(iter+1) = Big_phi_1;
        main_peakVal_store_1(iter+1) = Big_Val_1;
        main_peakLoc_store_2(iter+1) = Big_phi_2;
        main_peakVal_store_2(iter+1) = Big_Val_2;
        main_peak_skew_1(iter+1) = (phi_0_1-main_peakLoc_store_1(iter+1));
        main_peak_skew_2(iter+1) = (phi_0_2-main_peakLoc_store_2(iter+1));
        % Record values at focus angles for future analysis
        focus_value_store_1(iter+1) = interp1(phi, F_total, phi_0_1, 'linear', 'extrap');
        focus_value_store_2(iter+1) = interp1(phi, F_total, phi_0_2, 'linear', 'extrap');
    
        if isempty(peakVals)  % if there are no other sidelobes
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
            d_1 = mod(peakLocs - phi_0_1 + pi, 2*pi) - pi;
            d_2 = mod(peakLocs - phi_0_2 + pi, 2*pi) - pi;
            % Logical mask: 1 (true) if outside cone_rad, else 0 (false)
            validMask_cone_1 = abs(d_1) > cone_rad;   % logical array, same size as peakLocs
            validMask_cone_2 = abs(d_2) > cone_rad;   % logical array, same size as peakLocs
            %validMask_cone = %Code for identifying peaks inside cone bounds from focus phi_0
            validMask_cone = validMask_cone_1 & validMask_cone_2;
    
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
        fprintf('After Epoch %d: %d sidelobes above %.1f dB\n', iter+1, m, eps_dB);
        end        
    
        % Optional Pattern plot (after For LoopNeeds modification to include for loop iteration)
        if show_plots
            %lab_7 = "Plot (Step 16)(test)";
            lab_7 = "Plot of Corrected Pattern (Step 16: 'f_{new}')";
            % View function graph
            plot_pattern_v3(phi, F_total, 'label',lab_7, 'phi_0', phi_0, 'phi_s', phi_s, 'Slobe', Slobe, 'null_phi', null_phi ,'iter', iter, 'show_plots', true );
        end

        % Misc. Code At End Of While Loop
        bw1 = directivity_met_v2(phi, F_total, phi_0_1);
        bw2 = directivity_met_v2(phi, F_total, phi_0_2);
        directivity_metric_1_beamwidth_store_1(iter+1) = bw1.beamwidth;
        directivity_metric_1_beamwidth_store_2(iter+1) = bw2.beamwidth;
        % ---- Store the max sidelobe and its angle for this epoch ----
        if isempty(Slobe)
            % No sidelobes above threshold — store LOW dummy values
            %max_sidelobe_store(iter+1) = -Inf;
            max_sidelobe_store(iter+1) = NaN;
            max_side_phi_store(iter+1) = NaN;
        else
            % Slobe is already sorted largest → smallest
            max_sidelobe_store(iter+1) = Slobe(1);
            max_side_phi_store(iter+1) = phi_s(1);
        end
        iter = iter + 1; % increase iteration for the while loop        


    end % End of while loop



    %% ---- Additional Calculations ----
    % Find all local maxima (peaks) in the final pattern
        Fmag = abs(F_total);
        [peakVals, peakLocs] = findpeaks_circular(Fmag, phi);    
    % Identifying which of the lobes corresponds to phi_0_1 (the first focus). 
        [~, first_mainIdx] = min(abs(peakLocs - phi_0_1));    
    % Record and remove the peak corresponds to phi_0_1 (the first focus)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        Big_Val_final_1 = peakVals(first_mainIdx);
        Big_phi_final_1 = peakLocs(first_mainIdx);
        peakVals(first_mainIdx) = [];
        peakLocs(first_mainIdx)    = [];
    % Identifying which of the lobes corresponds to phi_0_2 (the second focus). 
        [~, second_mainIdx] = min(abs(peakLocs - phi_0_2));    
    % Record and remove the peak corresponds to phi_0_1 (the first focus)
        %peakVals_db = 10*log10((peakVals.^2) / (max(Fmag).^2));
        Big_Val_final_2 = peakVals(second_mainIdx);
        Big_phi_final_2 = peakLocs(second_mainIdx);
        peakVals(second_mainIdx) = [];
        peakLocs(second_mainIdx)    = [];
    % Calculate and record Max Sidelobe
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
    % Record Final value at focus angle 1
        F_at_phi_0_1 = interp1(phi, Fmag, phi_0_1, 'linear', 'extrap');
    % Record Final value at focus angle 2
        F_at_phi_0_2 = interp1(phi, Fmag, phi_0_2, 'linear', 'extrap');
    % Record Final value at Max Sidelobe value
        %max_sidelobe_final = phi_s_fin(1);
        %max_sidelobe_final = phi_s_fin;

    %% ---- Results ----
    final_epoch = iter-1;
    total_time = toc;

    % ---- Outputs ----
    results.final_epoch = final_epoch;
    results.final_iteration = iter;
    results.total_time  = total_time;
    results.cone_rad = cone_rad;
    results.final_function = abs(F_total);
    results.initial_function = abs(AF);    
    results.focus_angle_1 = phi_0_1;
    results.focus_angle_1_deg = round(rad2deg(phi_0_1));
    results.focus_angle_2 = phi_0_2;
    results.focus_angle_2_deg = round(rad2deg(phi_0_2));
    results.Big_Val_final_1 = Big_Val_final_1;
    results.Big_Val_final_2 = Big_Val_final_2;
    results.Big_phi_final_1 = Big_phi_final_1;
    results.Big_phi_final_2 = Big_phi_final_2;
    %results.max_sidelobe_final = max_sidelobe_final;
    results.max_sidelobe_store = max_sidelobe_store; 
    results.F_at_phi_0_1 = F_at_phi_0_1;
    results.F_at_phi_0_2 = F_at_phi_0_2;
%    results.max_side_phi_store = max_side_phi_store;
%    results.main_peakLoc_store = main_peakLoc_store;
    results.main_peakLoc_store_1 = main_peakLoc_store_1;
    results.main_peakLoc_store_2 = main_peakLoc_store_2;
    results.main_peakVal_store_1 = main_peakVal_store_1;
    results.main_peakVal_store_2 = main_peakVal_store_2;
    results.main_peak_skew_1 = main_peak_skew_1;
    results.main_peak_skew_2 = main_peak_skew_2;
    results.directivity_metric_1_beamwidth_store_1 = directivity_metric_1_beamwidth_store_1;
    results.directivity_metric_1_beamwidth_store_2 = directivity_metric_1_beamwidth_store_2;
%    results.phi_s_sorted_fin = phi_s_sorted_fin;
%    results.phi_s_fin = phi_s_fin;
%    results.Big_Val_final = Big_Val_final;
%    results.Big_phi_final = Big_phi_final;
%    results.F_at_phi_0 = abs(F_at_phi_0); % without imaginary component
    %results.F_at_phi_0 = F_at_phi_0; % with imaginary component
    %results.focus_value_store = focus_value_store; % with imaginary component
    results.focus_value_store_1 = abs(focus_value_store_1); % without imaginary component
    results.focus_value_store_2 = abs(focus_value_store_2); % without imaginary component

end