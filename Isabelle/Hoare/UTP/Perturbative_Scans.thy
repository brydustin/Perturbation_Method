theory Perturbative_Scans
  imports "Perturbative_Termination.Classify"
begin

section \<open>Facts about the scans of the perturbative method\<close>

text \<open>Used by the ITree/UTP proof in Perturbative_UTP.\<close>

subsection \<open>The run\<close>

lemma run_frozen:
  assumes "elig p N band tm (run p N band tm ts t n) t = {}"
  shows "run p N band tm ts t (n + k) = run p N band tm ts t n"
  using assms by (induction k) simp_all

text \<open>A run that has not stopped at step \<open>n\<close> stops later, so \<open>n\<close> is below the bound.\<close>
lemma busy_less:
  assumes "stops_within p N band tm ts t D"
    and "elig p N band tm (run p N band tm ts t n) t \<noteq> {}"
  shows "n < D"
proof -
  obtain n0 where n0: "n0 \<le> D" "elig p N band tm (run p N band tm ts t n0) t = {}"
    using assms(1) unfolding stops_within_def by blast
  have "n < n0"
  proof (rule ccontr)
    assume "\<not> n < n0"
    then have "run p N band tm ts t n = run p N band tm ts t n0"
      using run_frozen [OF n0(2), where k = "n - n0"] by simp
    with n0(2) assms(2) show False by simp
  qed
  with n0(1) show ?thesis by simp
qed

subsection \<open>Scans over the grid\<close>

text \<open>The indices below \<open>k\<close> where \<open>R\<close> holds, the largest and smallest value of \<open>f\<close> on them
  (or \<open>a\<close>), and agreement of two functions below \<open>k\<close>.\<close>

definition below :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat set" where
  "below R k = {q. q < k \<and> R q}"

definition max_below :: "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "max_below a f R k = Max (insert a (f ` below R k))"

definition min_below :: "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "min_below a f R k = Min (insert a (f ` below R k))"

definition agrees :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "agrees P f k \<longleftrightarrow> (\<forall>q<k. P q = f q)"

lemma finite_below: "finite (below R k)"
  unfolding below_def by simp

lemma below_0: "below R 0 = {}"
  unfolding below_def by simp

lemma below_Suc: "below R (Suc k) = (if R k then insert k (below R k) else below R k)"
  unfolding below_def by (auto simp: less_Suc_eq)

lemma max_below_0: "max_below a f R 0 = a"
  unfolding max_below_def below_0 by simp

lemma max_below_Suc:
  "max_below a f R (Suc k) = (if R k then max (max_below a f R k) (f k) else max_below a f R k)"
proof (cases "R k")
  case True
  then have e: "insert a (f ` below R (Suc k)) = insert (f k) (insert a (f ` below R k))"
    by (auto simp: below_Suc)
  have "Max (insert (f k) (insert a (f ` below R k))) = max (f k) (Max (insert a (f ` below R k)))"
    using finite_below by (intro Max_insert) auto
  then show ?thesis using True by (simp only: max_below_def e if_True max.commute)
next
  case False
  then show ?thesis by (simp only: max_below_def below_Suc if_False)
qed

lemma min_below_0: "min_below a f R 0 = a"
  unfolding min_below_def below_0 by simp

lemma min_below_Suc:
  "min_below a f R (Suc k) = (if R k then min (min_below a f R k) (f k) else min_below a f R k)"
proof (cases "R k")
  case True
  then have e: "insert a (f ` below R (Suc k)) = insert (f k) (insert a (f ` below R k))"
    by (auto simp: below_Suc)
  have "Min (insert (f k) (insert a (f ` below R k))) = min (f k) (Min (insert a (f ` below R k)))"
    using finite_below by (intro Min_insert) auto
  then show ?thesis using True by (simp only: min_below_def e if_True min.commute)
next
  case False
  then show ?thesis by (simp only: min_below_def below_Suc if_False)
qed

lemma agrees_0: "agrees P f 0"
  unfolding agrees_def by simp

lemma agrees_Suc: "agrees (P(k := v)) f (Suc k) \<longleftrightarrow> agrees P f k \<and> v = f k"
  unfolding agrees_def by (auto simp: less_Suc_eq)

lemma agrees_M: "agrees P f M \<longleftrightarrow> (\<forall>q<M. P q = f q)"
  unfolding agrees_def ..

subsection \<open>What the scans compute\<close>

lemma c0_lam: "(\<lambda>j. cnj (steer p t j)) = c0 p t"
  by (simp add: fun_eq_iff c0_def)

lemma corr_lam: "(\<lambda>j. w j - patt p N w (grid s) / of_nat N * cnj (steer p (grid s) j)) = corr p N s w"
  by (simp add: fun_eq_iff corr_def)

lemma sq_patt: "(cmod (patt p N w (grid k)))\<^sup>2 = sq p N w k"
  by (simp add: sq_def)

lemma sq_nonneg: "0 \<le> sq p N w m"
  by (simp add: sq_def)

lemma peak_pos:
  assumes "is_peak p N w m"
  shows "0 < sq p N w m"
proof -
  have "sq p N w (prev_idx m) < sq p N w m" using assms by (simp add: is_peak_def)
  moreover have "0 \<le> sq p N w (prev_idx m)" by (rule sq_nonneg)
  ultimately show ?thesis by linarith
qed

lemma sq_le_sqmax: "m < M \<Longrightarrow> sq p N w m \<le> sqmax p N w"
  unfolding sqmax_def by (rule Max_ge) auto

lemma max_below_sqmax: "max_below 0 (sq p N w) (\<lambda>q. True) M = sqmax p N w"
proof -
  have u: "below (\<lambda>q. True) M = {..<M}" unfolding below_def by auto
  have M0: "0 < M" by (simp add: M_def)
  have "sq p N w 0 \<le> Max (sq p N w ` {..<M})" using M0 by (intro Max_ge) auto
  then have "0 \<le> Max (sq p N w ` {..<M})" using sq_nonneg [of p N w 0] by linarith
  moreover have "sq p N w ` {..<M} \<noteq> {}" using M0 by auto
  ultimately show ?thesis unfolding max_below_def u sqmax_def by (simp add: max_absorb2)
qed

lemma peak_test:
  "(sq p N w (prev_idx k) < sq p N w k \<and> sq p N w (next_idx k) < sq p N w k) = is_peak p N w k"
  by (simp add: is_peak_def)

lemma below_peaks: "below (is_peak p N w) M = peaks p N w"
  unfolding below_def peaks_def ..

text \<open>The peaks nearest the focus: \<open>2\<pi>\<close> exceeds every circular distance.\<close>
lemma mains_below:
  "below (\<lambda>q. q \<in> peaks p N w \<and>
      cdist (grid q) t = min_below (2 * pi) (\<lambda>q. cdist (grid q) t) (\<lambda>q. q \<in> peaks p N w) M) M
    = mains p N w t"
    (is "below (\<lambda>q. _ \<and> _ = ?d) M = _")
proof -
  have K: "below (\<lambda>q. q \<in> peaks p N w) M = peaks p N w"
    unfolding below_def peaks_def by auto
  have d: "?d = Min (insert (2 * pi) ((\<lambda>q. cdist (grid q) t) ` peaks p N w))"
    unfolding min_below_def K ..
  have le: "?d \<le> cdist (grid q) t" if "q \<in> peaks p N w" for q
    unfolding d using finite_peaks that by (intro Min_le) auto
  have "?d \<in> insert (2 * pi) ((\<lambda>q. cdist (grid q) t) ` peaks p N w)"
    unfolding d using finite_peaks by (intro Min_in) auto
  then have at: "?d = 2 * pi \<or> (\<exists>q \<in> peaks p N w. ?d = cdist (grid q) t)" by auto
  show ?thesis
  proof (intro set_eqI iffI)
    fix m assume "m \<in> below (\<lambda>q. q \<in> peaks p N w \<and> cdist (grid q) t = ?d) M"
    then have m: "m \<in> peaks p N w" "cdist (grid m) t = ?d" unfolding below_def by auto
    then show "m \<in> mains p N w t" using le unfolding mains_def by auto
  next
    fix m assume "m \<in> mains p N w t"
    then have mp: "m \<in> peaks p N w" and min: "\<forall>q\<in>peaks p N w. cdist (grid m) t \<le> cdist (grid q) t"
      unfolding mains_def by auto
    have "?d \<le> cdist (grid m) t" using le mp by blast
    moreover have "cdist (grid m) t \<le> ?d"
    proof (cases "?d = 2 * pi")
      case True
      then show ?thesis using cdist_le_pi [of "grid m" t] pi_gt_zero by linarith
    next
      case False
      then obtain q where "q \<in> peaks p N w" "?d = cdist (grid q) t" using at by blast
      then show ?thesis using min by auto
    qed
    ultimately have "cdist (grid m) t = ?d" by linarith
    moreover have "m < M" using mp unfolding peaks_def by simp
    ultimately show "m \<in> below (\<lambda>q. q \<in> peaks p N w \<and> cdist (grid q) t = ?d) M"
      using mp unfolding below_def by simp
  qed
qed

text \<open>The loudest peaks of a set of peaks.\<close>
lemma sel_below:
  assumes E: "E \<subseteq> peaks p N w"
  shows "below (\<lambda>q. q \<in> E \<and> sq p N w q = max_below 0 (sq p N w) (\<lambda>q. q \<in> E) M) M = sel p N w E"
    (is "below (\<lambda>q. _ \<and> _ = ?b) M = _")
proof -
  have EM: "q < M" if "q \<in> E" for q using that E unfolding peaks_def by auto
  have K: "below (\<lambda>q. q \<in> E) M = E" using EM unfolding below_def by auto
  have b: "?b = Max (insert 0 (sq p N w ` E))" unfolding max_below_def K ..
  have fin: "finite E" using E finite_peaks by (rule finite_subset)
  have le: "sq p N w q \<le> ?b" if "q \<in> E" for q unfolding b using fin that by (intro Max_ge) auto
  have "?b \<in> insert 0 (sq p N w ` E)" unfolding b using fin by (intro Max_in) auto
  then have at: "?b = 0 \<or> (\<exists>q \<in> E. ?b = sq p N w q)" by auto
  show ?thesis
  proof (intro set_eqI iffI)
    fix q assume "q \<in> below (\<lambda>q. q \<in> E \<and> sq p N w q = ?b) M"
    then have q: "q \<in> E" "sq p N w q = ?b" unfolding below_def by auto
    then show "q \<in> sel p N w E" using le unfolding sel_def by auto
  next
    fix q assume "q \<in> sel p N w E"
    then have q: "q \<in> E" and top: "\<forall>m\<in>E. sq p N w m \<le> sq p N w q" unfolding sel_def by auto
    have "sq p N w q \<le> ?b" using le q by blast
    moreover have "?b \<le> sq p N w q"
    proof (cases "?b = 0")
      case True
      then show ?thesis using sq_nonneg [of p N w q] by simp
    next
      case False
      then obtain r where "r \<in> E" "?b = sq p N w r" using at by blast
      then show ?thesis using top by auto
    qed
    ultimately have "sq p N w q = ?b" by linarith
    then show "q \<in> below (\<lambda>q. q \<in> E \<and> sq p N w q = ?b) M"
      using q EM [OF q] unfolding below_def by simp
  qed
qed

text \<open>-20 dB is a power ratio of 1/100.\<close>
lemma dB_le_iff:
  fixes x y :: real
  assumes x: "0 < x" and y: "0 < y"
  shows "10 * log 10 (x / y) \<le> -20 \<longleftrightarrow> x \<le> y / 100"
proof -
  have p: "(10::real) powr (-2) = 1 / 100"
    by (simp add: powr_neg_numeral)
  have "10 * log 10 (x / y) \<le> -20 \<longleftrightarrow> log 10 (x / y) \<le> -2" by simp
  also have "\<dots> \<longleftrightarrow> x / y \<le> 10 powr (-2)"
    using x y by (intro log_le_iff) simp_all
  also have "\<dots> \<longleftrightarrow> x \<le> y / 100"
    using y unfolding p by (simp add: field_simps)
  finally show ?thesis .
qed

lemma dB_less_iff:
  fixes x y :: real
  assumes "0 < x" "0 < y"
  shows "-20 < 10 * log 10 (x / y) \<longleftrightarrow> y / 100 < x"
proof -
  have "\<not> 10 * log 10 (x / y) \<le> -20 \<longleftrightarrow> \<not> x \<le> y / 100" using dB_le_iff [OF assms] by simp
  then show ?thesis by (simp add: not_le)
qed

text \<open>MATLAB's eligibility test in decibels, in the form the simplifier leaves it.\<close>
lemma elig_test:
  "(k \<in> peaks p N w \<and> k \<noteq> tm (mains p N w t) \<and> - 2 < log 10 (sq p N w k / sqmax p N w) \<and>
     in_band band t k) = (k \<in> elig p N band tm w t)"
proof (cases "k \<in> peaks p N w")
  case True
  have pos: "0 < sq p N w k" using True by (simp add: peaks_def peak_pos)
  have "sq p N w k \<le> sqmax p N w" using True by (simp add: peaks_def sq_le_sqmax)
  then have pos2: "0 < sqmax p N w" using pos by linarith
  have "- 2 < log 10 (sq p N w k / sqmax p N w) \<longleftrightarrow> sqmax p N w / 100 < sq p N w k"
    using dB_less_iff [OF pos pos2] by simp
  then show ?thesis using True by (auto simp: elig_def eligible_def)
next
  case False
  then show ?thesis by (auto simp: elig_def eligible_def)
qed

lemma below_elig: "below (\<lambda>q. q \<in> elig p N band tm w t) M = elig p N band tm w t"
  using elig_subset_peaks [of p N band tm w t] unfolding below_def peaks_def by auto

text \<open>When nothing is eligible, every sidelobe outside the band is at or below -20 dB.\<close>
lemma stopped_dB:
  assumes E: "elig p N band tm w t = {}" and m: "m < M" "is_peak p N w m" "m \<noteq> tm (mains p N w t)"
    "in_band band t m"
  shows "10 * log 10 (sq p N w m / sqmax p N w) \<le> -20"
proof -
  have pos: "0 < sq p N w m" using m(2) by (rule peak_pos)
  have "sq p N w m \<le> sqmax p N w" using m(1) by (rule sq_le_sqmax)
  then have pos2: "0 < sqmax p N w" using pos by linarith
  have "m \<in> peaks p N w" using m(1,2) by (simp add: peaks_def)
  then have "\<not> sqmax p N w / 100 < sq p N w m"
    using E m(3,4) by (auto simp: elig_def eligible_def)
  then show ?thesis using dB_le_iff [OF pos pos2] by simp
qed

text \<open>The same in the form the simplifier leaves it.\<close>
lemma stopped_log:
  assumes "{} = elig p N band tm w t" "m < M" "is_peak p N w m" "m \<noteq> tm (mains p N w t)"
    "in_band band t m"
  shows "log 10 (sq p N w m / sqmax p N w) \<le> - 2"
  using stopped_dB [OF assms(1) [symmetric] assms(2-)] by simp

lemma less_M: "k \<le> M \<Longrightarrow> k \<noteq> M \<Longrightarrow> k < M"
  by arith

lemma variant_step: "n < D \<Longrightarrow> D - Suc n < D - n"
  by arith

lemmas scan_simps = below_0 below_Suc max_below_0 max_below_Suc min_below_0 min_below_Suc
  agrees_0 agrees_Suc agrees_M max_below_sqmax peak_test below_peaks mains_below sel_below
  elig_test below_elig elig_subset_peaks prev_lt next_lt less_M Suc_le_eq variant_step

end
