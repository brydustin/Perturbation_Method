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