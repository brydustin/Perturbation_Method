theory Perturbative_Basics
  imports "HOL-Analysis.Analysis"
begin

section \<open>Arrays, patterns and the correction step\<close>

text \<open>Positions in metres, 3 GHz, so \<open>k = 20\<pi>\<close>.  An array is a function from element
  indices to positions together with its element count \<open>N\<close>.  Grid \<open>\<phi>\<^sub>m = 2\<pi>m/M\<close>, \<open>M = 1000\<close>.\<close>

definition kw :: real where "kw = 20 * pi"

definition M :: nat where "M = 1000"

definition grid :: "nat \<Rightarrow> real" where "grid m = 2 * pi * real m / real M"

definition steer :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex" where
  "steer p \<phi> j = cis (kw * (fst (p j) * cos \<phi> + snd (p j) * sin \<phi>))"

definition patt :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> complex" where
  "patt p N c \<phi> = (\<Sum>j<N. steer p \<phi> j * c j)"

text \<open>Squared magnitude of the pattern at grid index \<open>m\<close>.\<close>
definition sq :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "sq p N c m = (cmod (patt p N c (grid m)))\<^sup>2"

text \<open>The initial excitation steered to the focus \<open>t\<close>: unit amplitudes, phases \<open>cnj (steer t)\<close>.\<close>
definition c0 :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex" where
  "c0 p t j = cnj (steer p t j)"

text \<open>One correction at grid index \<open>s\<close>.\<close>
definition corr :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex" where
  "corr p N s c j = c j - patt p N c (grid s) / of_nat N * cnj (steer p (grid s) j)"

lemma cmod_steer [simp]: "cmod (steer p \<phi> j) = 1"
  by (simp add: steer_def)

lemma steer_cnj_self: "steer p \<phi> j * cnj (steer p \<phi> j) = 1"
  by (simp add: steer_def complex_mult_cnj cmod_steer flip: norm_mult)

lemma sum_steer_cnj: "(\<Sum>j<N. steer p \<phi> j * cnj (steer p \<phi> j)) = of_nat N"
  by (simp add: steer_cnj_self)

text \<open>Lemma 2.1: a correction places a null at the corrected sample.\<close>
lemma patt_corr_self: "patt p N (corr p N s c) (grid s) = 0"
proof -
  have "patt p N (corr p N s c) (grid s)
      = patt p N c (grid s) - patt p N c (grid s) / of_nat N * (\<Sum>j<N. steer p (grid s) j * cnj (steer p (grid s) j))"
    by (simp add: patt_def corr_def algebra_simps sum_subtractf sum_distrib_left)
  also have "\<dots> = patt p N c (grid s) - patt p N c (grid s) / of_nat N * of_nat N"
    by (simp add: sum_steer_cnj)
  finally show ?thesis by (cases "N = 0") (simp_all add: patt_def)
qed

section \<open>Focus-independent rows (Lemma 2.2)\<close>

text \<open>\<open>g m s = a(\<phi>\<^sub>m)\<^sup>T cnj a(\<phi>\<^sub>s) / N\<close>.\<close>
definition gram :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "gram p N m s = (\<Sum>j<N. steer p (grid m) j * cnj (steer p (grid s) j)) / of_nat N"

text \<open>Sequences of corrections are lists with the most recent correction first.\<close>
primrec rows :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "rows p N [] m j = steer p (grid m) j"
| "rows p N (s # \<sigma>) m j = rows p N \<sigma> m j - gram p N m s * rows p N \<sigma> s j"

primrec exc :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> complex" where
  "exc p N c [] = c"
| "exc p N c (s # \<sigma>) = corr p N s (exc p N c \<sigma>)"

lemma patt_corr:
  "patt p N (corr p N s c) (grid m) = patt p N c (grid m) - gram p N m s * patt p N c (grid s)"
  by (simp add: patt_def corr_def gram_def sum_subtractf sum_distrib_left sum_divide_distrib
                algebra_simps)

text \<open>The pattern after the corrections \<open>\<sigma>\<close> is a fixed linear function of the initial excitation.\<close>
lemma patt_exc_rows: "patt p N (exc p N c \<sigma>) (grid m) = (\<Sum>j<N. rows p N \<sigma> m j * c j)"
proof (induction \<sigma> arbitrary: m)
  case Nil
  show ?case by (simp add: patt_def)
next
  case (Cons s \<sigma>)
  have "patt p N (exc p N c (s # \<sigma>)) (grid m)
      = patt p N (exc p N c \<sigma>) (grid m) - gram p N m s * patt p N (exc p N c \<sigma>) (grid s)"
    by (simp add: patt_corr)
  also have "\<dots> = (\<Sum>j<N. rows p N \<sigma> m j * c j) - gram p N m s * (\<Sum>j<N. rows p N \<sigma> s j * c j)"
    by (simp add: Cons.IH)
  also have "\<dots> = (\<Sum>j<N. rows p N (s # \<sigma>) m j * c j)"
    by (simp add: sum_subtractf sum_distrib_left algebra_simps)
  finally show ?case .
qed

section \<open>Strict peaks (Lemma 2.6)\<close>

definition prev_idx :: "nat \<Rightarrow> nat" where "prev_idx m = (m + M - 1) mod M"
definition next_idx :: "nat \<Rightarrow> nat" where "next_idx m = (m + 1) mod M"

definition is_peak :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_peak p N c m \<longleftrightarrow> sq p N c m > sq p N c (prev_idx m) \<and> sq p N c m > sq p N c (next_idx m)"

lemma prev_next: "m < M \<Longrightarrow> prev_idx (next_idx m) = m"
  unfolding prev_idx_def next_idx_def M_def by (cases "m = 999") auto

lemma adjacent_not_both_peaks:
  assumes "m < M" "is_peak p N c m" "is_peak p N c (next_idx m)"
  shows False
  using assms prev_next [OF assms(1)] unfolding is_peak_def by auto

end
