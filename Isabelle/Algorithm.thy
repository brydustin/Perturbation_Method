theory Algorithm
  imports Taylor_Enclosure
begin

section \<open>Circular distance (Lemma 2.5)\<close>

definition cdist :: "real \<Rightarrow> real \<Rightarrow> real" where
  "cdist a b = \<bar>(a - b) - 2 * pi * of_int (round ((a - b) / (2 * pi)))\<bar>"

lemma two_pi_abs: "2 * pi * \<bar>y / (2 * pi) - z\<bar> = \<bar>y - 2 * pi * z\<bar>"
proof -
  have "2 * pi * \<bar>y / (2 * pi) - z\<bar> = \<bar>2 * pi * (y / (2 * pi) - z)\<bar>" by (simp add: abs_mult)
  also have "2 * pi * (y / (2 * pi) - z) = y - 2 * pi * z" by (simp add: field_simps)
  finally show ?thesis .
qed

lemma cdist_min: "cdist a b \<le> \<bar>(a - b) - 2 * pi * of_int n\<bar>"
  unfolding cdist_def two_pi_abs [symmetric]
  by (intro mult_left_mono round_diff_minimal) simp

lemma cdist_nonneg: "0 \<le> cdist a b"
  by (simp add: cdist_def)

lemma cdist_le_pi: "cdist a b \<le> pi"
proof -
  have "2 * pi * \<bar>(a - b) / (2 * pi) - of_int (round ((a - b) / (2 * pi)))\<bar> \<le> 2 * pi * (1 / 2)"
    using of_int_round_abs_le [of "(a - b) / (2 * pi)"] by (intro mult_left_mono) (simp_all add: abs_minus_commute)
  then show ?thesis unfolding cdist_def two_pi_abs [symmetric] by simp
qed

lemma cdist_sym_le: "cdist b a \<le> cdist a b"
proof -
  define r where "r = round ((a - b) / (2 * pi))"
  have "cdist b a \<le> \<bar>(b - a) - 2 * pi * of_int (- r)\<bar>" by (rule cdist_min)
  also have "(b - a) - 2 * pi * of_int (- r) = - ((a - b) - 2 * pi * of_int r)" by simp
  also have "\<bar>- ((a - b) - 2 * pi * of_int r)\<bar> = cdist a b" unfolding cdist_def r_def by (rule abs_minus_cancel)
  finally show ?thesis .
qed

lemma cdist_sym: "cdist a b = cdist b a"
  using cdist_sym_le [of a b] cdist_sym_le [of b a] by simp

text \<open>The circular distance is 1-Lipschitz in each argument.\<close>
lemma cdist_lipschitz: "\<bar>cdist a t - cdist a t'\<bar> \<le> \<bar>t - t'\<bar>"
proof -
  have le: "cdist a t \<le> cdist a t' + \<bar>t - t'\<bar>" for t t'
  proof -
    define r where "r = round ((a - t') / (2 * pi))"
    have "cdist a t \<le> \<bar>(a - t) - 2 * pi * of_int r\<bar>" by (rule cdist_min)
    also have "(a - t) - 2 * pi * of_int r = ((a - t') - 2 * pi * of_int r) + (t' - t)" by simp
    also have "\<bar>((a - t') - 2 * pi * of_int r) + (t' - t)\<bar> \<le> \<bar>(a - t') - 2 * pi * of_int r\<bar> + \<bar>t' - t\<bar>"
      by (rule abs_triangle_ineq)
    also have "\<bar>(a - t') - 2 * pi * of_int r\<bar> = cdist a t'" unfolding cdist_def r_def ..
    finally show ?thesis by (simp only: abs_minus_commute)
  qed
  have a: "cdist a t - cdist a t' \<le> \<bar>t - t'\<bar>" using le [of t t'] by simp
  have b: "- (cdist a t - cdist a t') \<le> \<bar>t - t'\<bar>" using le [of t' t] by (simp add: abs_minus_commute)
  show ?thesis by (rule abs_leI [OF a b])
qed

section \<open>The algorithm (Definitions 1.1 and 1.2)\<close>

text \<open>The band: \<open>None\<close> for no guard band, \<open>Some \<Delta>\<close> for the half-width \<open>\<Delta>\<close> in radians.\<close>

definition sqmax :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real" where
  "sqmax p N c = Max ((sq p N c) ` {..<M})"

definition peaks :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat set" where
  "peaks p N c = {m. m < M \<and> is_peak p N c m}"

definition mains :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "mains p N c t = {m \<in> peaks p N c. \<forall>q \<in> peaks p N c. cdist (grid m) t \<le> cdist (grid q) t}"

definition in_band :: "real option \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "in_band band t m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some \<Delta> \<Rightarrow> cdist (grid m) t > \<Delta>)"

definition eligible :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat set" where
  "eligible p N band c t m0 = {m \<in> peaks p N c. m \<noteq> m0 \<and> sq p N c m > sqmax p N c / 100 \<and> in_band band t m}"

definition sel :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat set \<Rightarrow> nat set" where
  "sel p N c E = {s \<in> E. \<forall>m \<in> E. sq p N c m \<le> sq p N c s}"

text \<open>A tie rule is a pair of choice functions; \<open>tie_rule\<close> says they choose elements.\<close>
definition tie_rule :: "(nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> bool" where
  "tie_rule tm ts \<longleftrightarrow> (\<forall>S. S \<noteq> {} \<and> finite S \<longrightarrow> tm S \<in> S) \<and> (\<forall>S. S \<noteq> {} \<and> finite S \<longrightarrow> ts S \<in> S)"

text \<open>The eligible set after the main lobe has been chosen by the tie rule.\<close>
definition elig :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "elig p N band tm c t = eligible p N band c t (tm (mains p N c t))"

text \<open>The state after \<open>n\<close> corrections; it freezes once nothing is eligible.\<close>
primrec run :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "run p N band tm ts t 0 = c0 p t"
| "run p N band tm ts t (Suc n) =
     (if elig p N band tm (run p N band tm ts t n) t = {} then run p N band tm ts t n
      else corr p N (ts (sel p N (run p N band tm ts t n) (elig p N band tm (run p N band tm ts t n) t))) (run p N band tm ts t n))"

definition stops_within :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "stops_within p N band tm ts t D \<longleftrightarrow> (\<exists>n \<le> D. elig p N band tm (run p N band tm ts t n) t = {})"

text \<open>The corrected indices, most recent first, as long as the run has not stopped.\<close>
primrec corrs :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat list" where
  "corrs p N band tm ts t 0 = []"
| "corrs p N band tm ts t (Suc n) =
     (if elig p N band tm (run p N band tm ts t n) t = {} then corrs p N band tm ts t n
      else ts (sel p N (run p N band tm ts t n) (elig p N band tm (run p N band tm ts t n) t)) # corrs p N band tm ts t n)"

lemma run_exc: "run p N band tm ts t n = exc p N (c0 p t) (corrs p N band tm ts t n)"
  by (induction n) simp_all

lemma finite_peaks: "finite (peaks p N c)"
  by (simp add: peaks_def)

lemma elig_subset_peaks: "elig p N band tm c t \<subseteq> peaks p N c"
  by (auto simp: elig_def eligible_def)

lemma finite_elig: "finite (elig p N band tm c t)"
  by (rule finite_subset [OF elig_subset_peaks finite_peaks])

text \<open>The selected index is a loudest eligible one (used by the soundness proof).\<close>
lemma sel_nonempty:
  assumes "E \<noteq> {}" "finite E"
  shows "sel p N c E \<noteq> {}"
proof -
  have "Max (sq p N c ` E) \<in> sq p N c ` E"
    using assms by (intro Max_in) simp_all
  then obtain s where s: "s \<in> E" "sq p N c s = Max (sq p N c ` E)" by auto
  have "sq p N c m \<le> sq p N c s" if "m \<in> E" for m
    using that assms s by (simp add: Max_ge)
  with s show ?thesis by (auto simp: sel_def)
qed

lemma sel_subset: "sel p N c E \<subseteq> E"
  by (auto simp: sel_def)

end
