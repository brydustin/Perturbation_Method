function [pv, pl] = findpeaks_fast(Fmag, phi_vec)
%FINDPEAKS_FAST  Vectorized strict-greater-than circular peak finder.
%   Drop-in replacement for findpeaks_circular for smooth array-factor
%   patterns. ~50-100x faster: no padding, no findpeaks call, no dedup
%   loop. Returns row vectors.
%
%   Caveat: strict '>' on both circular neighbors. On exact plateaus
%   (neighbors equal) no peak is reported; for smooth complex array
%   factors this is effectively impossible.
    Fmag    = Fmag(:).';
    phi_vec = phi_vec(:).';
    isPk = Fmag > Fmag([end 1:end-1]) & Fmag > Fmag([2:end 1]);
    pv = Fmag(isPk);
    pl = phi_vec(isPk);
end
