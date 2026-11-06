%% Pattern Plotting Function for Perturbative Method Code
% Version 5: Multi-focus, Multi-null, Big-phi, and cone-boundary support
% 11/20/2025
function plot_pattern_v5(phi, F_total, varargin)

    %% -------- InputParser Setup --------
    p = inputParser;
    p.FunctionName = 'plot_pattern_v5';

    % Required
    addRequired(p, 'phi',      @isnumeric);
    addRequired(p, 'F_total',  @isnumeric);

    % Optional name–value parameters
    addParameter(p, 'iter', 0, @isnumeric);

    addParameter(p, 'phi_0',    [], @isnumeric);  % vector of focus angles
    addParameter(p, 'phi_s',    [], @isnumeric);
    addParameter(p, 'Slobe',    [], @isnumeric);

    addParameter(p, 'label',    "", @(s) isstring(s) || ischar(s));
    addParameter(p, 'outdir',   "", @(s) isstring(s) || ischar(s));

    addParameter(p, 'null_phi', [], @isnumeric);  % vector
    addParameter(p, 'show_plots', false, @islogical);
    addParameter(p, 'save_plots', false, @islogical);

    addParameter(p, 'cone_rad', [], @isnumeric);   % for cone boundaries
    addParameter(p, 'Big_phi', [], @isnumeric);    % direction of actual main lobe peak
    
    addParameter(p, 'bw_edges_left',  [], @isnumeric);
    addParameter(p, 'bw_edges_right', [], @isnumeric);

    % Parse
    parse(p, phi, F_total, varargin{:});
    args = p.Results;

    % Extract
    phi        = args.phi;
    F_total    = args.F_total;
    phi_0      = args.phi_0(:);
    phi_s      = args.phi_s(:);
    Slobe      = args.Slobe(:);
    null_phi   = args.null_phi(:);
    cone_rad   = args.cone_rad;
    Big_phi    = args.Big_phi;

    label      = string(args.label);
    outdir     = string(args.outdir);
    show_plots = args.show_plots;
    save_plots = args.save_plots;
    iter       = args.iter;
    bw_left  = args.bw_edges_left(:);
    bw_right = args.bw_edges_right(:);


    if ~show_plots
        return;
    end

    %% -------- Compute normalized pattern --------
    Fdb = 10*log10(abs(F_total).^2 / max(abs(F_total).^2));
    Fdb(Fdb < -40) = -40;

    %% -------- Plot base pattern --------
    figure;
    hPat = polarplot(phi, Fdb, 'b'); hold on;
    rlim([-40 0]);
    rline = rlim;

    legendHandles = hPat;
    legendNames   = {"Pattern"};

    %% ========================================================
    %%  Focus Direction(s) — Green
    %% ========================================================
    %% -------- Focus direction(s) --------
    if ~isempty(phi_0)
        hFocusRep = [];  % representative line for legend
    
        for k = 1:numel(phi_0)
            hF = polarplot([phi_0(k) phi_0(k)], rline, 'g', 'LineWidth', 2);
            if isempty(hFocusRep)
                hFocusRep = hF;
            end
        end
    
        legendHandles(end+1) = hFocusRep;
        legendNames{end+1}   = sprintf("Focus (%d)", numel(phi_0));
    end

    %% ========================================================
    %%  Sidelobes — Red
    %% ========================================================
    if ~isempty(phi_s)
        rmin = rline(1);
        hSideLegend = polarplot([phi_s(1) phi_s(1)], [rmin Slobe(1)], ...
                                'r', 'LineWidth', 1.5);

        for k = 1:numel(phi_s)
            polarplot([phi_s(k) phi_s(k)], [rmin Slobe(k)], ...
                      'r', 'LineWidth', 1.5);
        end

        polarplot(phi_s, Slobe, 'ro', 'MarkerFaceColor','r');

        legendHandles(end+1) = hSideLegend;
        legendNames{end+1}   = sprintf("Sidelobes (%d)", numel(phi_s));
    end

    %% ========================================================
    %%  Null Directions — Black
    %% ========================================================
    if ~isempty(null_phi)
        for k = 1:numel(null_phi)
            hNull = polarplot([null_phi(k) null_phi(k)], rline, ...
                               'k', 'LineWidth', 2);
        end

        legendHandles(end+1) = hNull;
        legendNames{end+1}   = sprintf("Nulls (%d)", numel(null_phi));
    end

%% ========================================================
%%  Big-phi (true main-beam direction) — Orange (multi supported)
%% ========================================================
if ~isempty(Big_phi)

    Big_phi = Big_phi(:);   % force column
    hBigRep = [];

    for k = 1:numel(Big_phi)
        hB = polarplot([Big_phi(k) Big_phi(k)], rline, ...
            'Color', [1 0.5 0], 'LineWidth', 2);  % orange

        if isempty(hBigRep)
            hBigRep = hB;   % representative handle for legend
        end
    end

    legendHandles(end+1) = hBigRep;
    legendNames{end+1}  = sprintf("Big-\\phi (%d)", numel(Big_phi));
end


    %% ========================================================
    %%  Cone Boundary Lines (phi_0 ± cone_rad) — Purple
    %% ========================================================
    %% -------- Cone Boundaries --------
    if ~isempty(cone_rad) && ~isempty(phi_0)
        hConeRep = [];
    
        for k = 1:numel(phi_0)
            ang1 = phi_0(k) + cone_rad;
            ang2 = phi_0(k) - cone_rad;
    
%            C1 = polarplot([ang1 ang1], rline, ...
%                           'Color', [0.5 0 0.8], 'LineWidth', 1.5);
%            C2 = polarplot([ang2 ang2], rline, ...
%                           'Color', [0.5 0 0.8], 'LineWidth', 1.5);
            C1 = polarplot([ang1 ang1], rline, ...
                           'Color', [0.9, 1.0, 0.0], 'LineWidth', 1.5);
            C2 = polarplot([ang2 ang2], rline, ...
                           'Color', [0.9, 1.0, 0.0], 'LineWidth', 1.5);            
    
            if isempty(hConeRep)
                hConeRep = C1;  % single representative for legend
            end
        end
    
        legendHandles(end+1) = hConeRep;
        legendNames{end+1}   = "Cone Bounds";
    end

%% ========================================================
%%  Half-Power Edges — Magenta
%% ========================================================
if ~isempty(bw_left) || ~isempty(bw_right)

    % Must match lengths if both present
    if ~isempty(bw_left) && ~isempty(bw_right)
        if numel(bw_left) ~= numel(bw_right)
            error("bw_edges_left and bw_edges_right must have the same length.");
        end
    end

    % Determine number of entries
    N = max(numel(bw_left), numel(bw_right));

    hBWrep = [];

    for k = 1:N

        % Left edge
        if ~isempty(bw_left)
            L = bw_left(k);
            if ~isnan(L)
                hL = polarplot([L L], rline, ...
                    'Color', [0.8 0 0.8], 'LineWidth', 2); % magenta
                if isempty(hBWrep)
                    hBWrep = hL;  % representative for legend
                end
            end
        end

        % Right edge
        if ~isempty(bw_right)
            R = bw_right(k);
            if ~isnan(R)
                polarplot([R R], rline, ...
                    'Color', [0.8 0 0.8], 'LineWidth', 2);
            end
        end

    end

    if ~isempty(hBWrep)
        legendHandles(end+1) = hBWrep;
        legendNames{end+1} = "Half-Power Edges";
    end

end

    
    %% -------- Title & Legend --------
    title(gca, label);
    subtitle(gca, sprintf("Iteration = %d", iter));
    legend(legendHandles, legendNames, 'Location', 'bestoutside');

    %% -------- Save --------
    if save_plots && strlength(outdir) > 0
        fname = fullfile(outdir, sprintf('%s_iter_%03d.png', label, iter));
        exportgraphics(gcf, fname, 'Resolution', 300);
    end

    hold off;
    drawnow;

end
