program perturb_ann "(p :: nat \<Rightarrow> real \<times> real, N :: nat, band :: real option, tm :: nat set \<Rightarrow> nat,
    ts :: nat set \<Rightarrow> nat, t :: real, D :: nat)" over pstate =
"w := (\<lambda>j. cnj (steer p t j)); n := 0;
 scan (p, N, band, tm, t);
 while E \<noteq> {}
   invariant w = Algorithm.run p N band tm ts t n \<and> n \<le> D \<and> (\<forall>q<M. P q = sq p N w q) \<and>
     m0 = tm (mains p N w t) \<and> E = elig p N band tm w t
   variant D - n
 do
   k := 0; best := 0;
   while k \<noteq> M
     invariant w = old:w \<and> n = old:n \<and> P = old:P \<and> E = old:E \<and> m0 = old:m0 \<and> k \<le> M \<and>
       best = max_below 0 (sq p N w) (\<lambda>q. q \<in> E) k
     variant M - k
   do if k \<in> E then best := max best (P k) fi; k := k + 1 od;
   k := 0; Ls := {};
   while k \<noteq> M
     invariant w = old:w \<and> n = old:n \<and> P = old:P \<and> E = old:E \<and> m0 = old:m0 \<and> best = old:best \<and>
       k \<le> M \<and> Ls = below (\<lambda>q. q \<in> E \<and> sq p N w q = best) k
     variant M - k
   do if k \<in> E \<and> P k = best then Ls := insert k Ls fi; k := k + 1 od;
   ms := ts Ls;
   w := (\<lambda>j. w j - patt p N w (grid ms) / of_nat N * cnj (steer p (grid ms) j));
   n := n + 1;
   scan (p, N, band, tm, t)
 od"
