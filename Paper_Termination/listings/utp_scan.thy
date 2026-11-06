program scan "(p :: nat \<Rightarrow> real \<times> real, N :: nat, band :: real option, tm :: nat set \<Rightarrow> nat, t :: real)"
  over pstate =
"k := 0; Pmax := 0;
 while k \<noteq> M
   invariant w = old:w \<and> n = old:n \<and> k \<le> M \<and> agrees P (sq p N w) k \<and>
     Pmax = max_below 0 (sq p N w) (\<lambda>q. True) k
   variant M - k
 do P := fupd P k ((cmod (patt p N w (grid k)))\<^sup>2); Pmax := max Pmax (P k); k := k + 1 od;
 k := 0; pk := {};
 while k \<noteq> M
   invariant w = old:w \<and> n = old:n \<and> P = old:P \<and> Pmax = old:Pmax \<and> k \<le> M \<and>
     pk = below (is_peak p N w) k
   variant M - k
 do if P (prev_idx k) < P k \<and> P (next_idx k) < P k then pk := insert k pk fi; k := k + 1 od;
 k := 0; dmin := 2 * pi;
 while k \<noteq> M
   invariant w = old:w \<and> n = old:n \<and> P = old:P \<and> Pmax = old:Pmax \<and> pk = old:pk \<and> k \<le> M \<and>
     dmin = min_below (2 * pi) (\<lambda>q. cdist (grid q) t) (\<lambda>q. q \<in> pk) k
   variant M - k
 do if k \<in> pk then dmin := min dmin (cdist (grid k) t) fi; k := k + 1 od;
 k := 0; Mn := {};
 while k \<noteq> M
   invariant w = old:w \<and> n = old:n \<and> P = old:P \<and> Pmax = old:Pmax \<and> pk = old:pk \<and>
     dmin = old:dmin \<and> k \<le> M \<and> Mn = below (\<lambda>q. q \<in> pk \<and> cdist (grid q) t = dmin) k
   variant M - k
 do if k \<in> pk \<and> cdist (grid k) t = dmin then Mn := insert k Mn fi; k := k + 1 od;
 m0 := tm Mn;
 k := 0; E := {};
 while k \<noteq> M
   invariant w = old:w \<and> n = old:n \<and> P = old:P \<and> Pmax = old:Pmax \<and> pk = old:pk \<and>
     m0 = old:m0 \<and> k \<le> M \<and> E = below (\<lambda>q. q \<in> elig p N band tm w t) k
   variant M - k
 do if k \<in> pk \<and> k \<noteq> m0 \<and> 10 * log 10 (P k / Pmax) > -20 \<and> in_band band t k then E := insert k E fi;
   k := k + 1 od"
