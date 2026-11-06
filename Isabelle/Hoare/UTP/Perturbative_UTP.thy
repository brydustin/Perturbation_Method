theory Perturbative_UTP
  imports Perturbative_Scans "ITree_VCG.ITree_VCG"
begin

section \<open>The perturbative method as an ITree program\<close>

text \<open>The program is perturb_method_v25b.m with one correction per iteration and no null,
  written in the ITree/UTP language.  A scan computes the pattern power on the
  grid, the strict peaks, the main lobe (the peak nearest the focus) and the peaks above -20 dB
  outside the band.  The main loop corrects the loudest of these and scans again; it runs while one
  exists and has no iteration cap.  Ties are broken by arbitrary choice functions tm and ts.\<close>

definition fupd :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "fupd f i v = fun_upd f i v"

lemma agrees_fupd: "agrees (fupd P k v) f (Suc k) \<longleftrightarrow> agrees P f k \<and> v = f k"
  unfolding fupd_def by (rule agrees_Suc)

lemma fupd_at: "fupd P k v k = v"
  by (simp add: fupd_def)

text \<open>Eligibility unfolded, and a run with an eligible sidelobe at step \<open>n\<close> has \<open>n\<close> below the bound.\<close>

lemma elig_mem:
  "(k \<in> elig p N band tm w t) =
     (k \<in> peaks p N w \<and> k \<noteq> tm (mains p N w t) \<and> - 2 < log 10 (sq p N w k / sqmax p N w) \<and>
      in_band band t k)"
  by (rule elig_test [symmetric])

lemma busy_mem:
  assumes "stops_within p N band tm ts t D" "x \<in> elig p N band tm (Algorithm.run p N band tm ts t n) t"
  shows "n < D"
  using assms by (intro busy_less) auto

text \<open>A loop followed by more code: the precondition and the invariant at exit hold before the rest.
  (Stated with \<open>literal_variables\<close> off, so that \<open>P\<close>, \<open>G\<close>, ... range over expressions.)\<close>

declare [[literal_variables = false]]

lemma thl_while_seq [hoare_safe]:
  assumes
    "\<And> old z. H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old) \<and> G \<and> Var = \<guillemotleft>z\<guillemotright>] Body [@(Inv old) \<and> Var < \<guillemotleft>z\<guillemotright>]"
    "\<And> old. `P \<and> \<guillemotleft>old\<guillemotright> = $\<^bold>v \<longrightarrow> @(Inv old)`"
    "\<And> old. H[\<not> G \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)] Rest [Post]"
  shows "H[P] (while G inv @(Inv old) var Var do Body od) ;; Rest [Post]"
proof (rule_tac thl_prestate)
  fix old
  have "\<And> z. H[(P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)) \<and> G \<and> Var = \<guillemotleft>z\<guillemotright>] Body [(P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)) \<and> Var < \<guillemotleft>z\<guillemotright>]"
  proof (simp, rule thl_frame_rule')
    fix z
    show "Body nmods P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>"
      by (expr_simp add: not_modifies_def)
    show "\<And> z. H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old) \<and> G \<and> Var = \<guillemotleft>z\<guillemotright>] Body [@(Inv old) \<and> Var < \<guillemotleft>z\<guillemotright>]"
      by (fact assms(1))
  qed
  hence w: "H[P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)] while G do Body od [\<not> G \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)]"
    by (rule thl_while)
  have w': "H[\<guillemotleft>old\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>] while G do Body od [\<not> G \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk> \<and> @(Inv old)]"
    using assms(2) by (rule_tac thl_conseq[OF w]; expr_auto)
  show "H[\<guillemotleft>old\<guillemotright> = $\<^bold>v \<and> P\<lbrakk>\<guillemotleft>old\<guillemotright>/\<^bold>v\<rbrakk>] (while G inv @(Inv old) var Var do Body od) ;; Rest [Post]"
    unfolding while_inv_var_def by (rule thl_seq [OF w' assms(3)])
qed

declare [[literal_variables]]

subsection \<open>State and programs\<close>

text \<open>State: excitation \<open>w\<close> (A_eff), corrections \<open>n\<close> (iter), powers \<open>P\<close> (|F|^2) and their
  maximum \<open>Pmax\<close>, grid index \<open>k\<close>, peaks \<open>pk\<close>, distance \<open>dmin\<close> and candidates \<open>Mn\<close> of the main
  lobe \<open>m0\<close>, eligible sidelobes \<open>E\<close>, the loudest power \<open>best\<close> with its peaks \<open>Ls\<close>, and the
  corrected index \<open>ms\<close>.\<close>

text \<open>Store variables need a default value.\<close>

instantiation real :: default
begin
definition "default_real = (0::real)"
instance ..
end

instantiation complex :: default
begin
definition "default_complex = (0::complex)"
instance ..
end

instantiation "fun" :: (type, default) default
begin
definition "default_fun = (\<lambda>_. default)"
instance ..
end

zstore pstate =
  w :: "nat \<Rightarrow> complex"
  n :: nat
  P :: "nat \<Rightarrow> real"
  Pmax :: real
  k :: nat
  pk :: "nat set"
  dmin :: real
  Mn :: "nat set"
  m0 :: nat
  E :: "nat set"
  best :: real
  Ls :: "nat set"
  ms :: nat

text \<open>The scan.  Each loop states what it computes from the variables it does not change
  (\<open>x = old:x\<close> is the value of \<open>x\<close> on entry to the loop).\<close>

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

text \<open>The method.  \<open>perturb_ann\<close> is \<open>perturb\<close> with the main loop annotated; \<open>D\<close> occurs only in
  the annotation.\<close>

program perturb "(p :: nat \<Rightarrow> real \<times> real, N :: nat, band :: real option, tm :: nat set \<Rightarrow> nat,
    ts :: nat set \<Rightarrow> nat, t :: real)" over pstate =
"w := (\<lambda>j. cnj (steer p t j)); n := 0;
 scan (p, N, band, tm, t);
 while E \<noteq> {}
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

lemma perturb_ann_is_perturb: "perturb_ann (p, N, band, tm, ts, t, D) = perturb (p, N, band, tm, ts, t)"
  by (simp add: perturb_ann_def perturb_def while_inv_var_def)

subsection \<open>Total correctness\<close>

theorem perturb_ann_correct:
  assumes stop: "stops_within p N band tm ts t D"
  shows "H[True] perturb_ann (p, N, band, tm, ts, t, D)
    [w = Algorithm.run p N band tm ts t n \<and> n \<le> D \<and> m0 = tm (mains p N w t) \<and>
     (\<forall>m<M. is_peak p N w m \<and> m \<noteq> m0 \<and> in_band band t m \<longrightarrow>
        10 * log 10 (sq p N w m / sqmax p N w) \<le> -20)]"
  unfolding perturb_ann_def scan_def
  apply (simp only: prod.case kcomp_assoc)
  apply vcg
  apply (simp_all only: fun_eq_iff [symmetric] c0_lam corr_lam sq_patt)
  apply (simp_all add: scan_simps agrees_fupd fupd_at busy_less [OF stop])
  apply (auto simp: c0_def corr_def dest: busy_mem [OF stop] intro: stopped_log)
  apply (auto simp: below_def is_peak_def elig_mem less_Suc_eq)
  done

text \<open>The same for the program without annotations.\<close>

corollary perturb_correct:
  assumes "stops_within p N band tm ts t D"
  shows "H[True] perturb (p, N, band, tm, ts, t)
    [w = Algorithm.run p N band tm ts t n \<and> n \<le> D \<and> m0 = tm (mains p N w t) \<and>
     (\<forall>m<M. is_peak p N w m \<and> m \<noteq> m0 \<and> in_band band t m \<longrightarrow>
        10 * log 10 (sq p N w m / sqmax p N w) \<le> -20)]"
  using perturb_ann_correct [OF assms] by (simp only: perturb_ann_is_perturb)

ML \<open>writeln ("oracles: " ^ commas (map (#1 o #1) (Thm_Deps.all_oracles [@{thm perturb_correct}])))\<close>

end
