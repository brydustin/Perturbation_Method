theory Circular_Floor
  imports Interval_Model
begin

section \<open>The circular array and the sidelobe region\<close>

text \<open>32 elements on a circle of radius \<open>2/5\<close> m (\<open>4\<lambda>\<close> at 3 GHz); focus \<open>0\<close>; band \<open>\<Delta>\<close> in degrees.\<close>

definition rc :: real where "rc = 2 / 5"
definition theta :: "nat \<Rightarrow> real" where "theta j = 2 * pi * real j / 32"
definition ucp :: "nat \<Rightarrow> real \<times> real" where "ucp j = (rc * cos (theta j), rc * sin (theta j))"

abbreviation Fc :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex" where "Fc c m \<equiv> patt ucp 32 c (grid m)"

text \<open>\<open>d(\<phi>\<^sub>m, 0) = 0.36 min(m, M-m)\<close> degrees, so the sidelobe region for the band \<open>\<Delta>\<close> degrees is\<close>
definition Qset :: "nat \<Rightarrow> nat set" where "Qset \<Delta> = {m. m < M \<and> 100 * \<Delta> < 36 * min m (M - m)}"

lemma Qset_subset: "Qset \<Delta> \<subseteq> {..<M}" unfolding Qset_def by auto
lemma finite_Qset: "finite (Qset \<Delta>)" using Qset_subset by (rule finite_subset) simp

definition maxQ :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real" where
  "maxQ \<Delta> c = Max ((\<lambda>q. cmod (Fc c q)) ` Qset \<Delta>)"
definition maxAll :: "(nat \<Rightarrow> complex) \<Rightarrow> real" where
  "maxAll c = Max ((\<lambda>m. cmod (Fc c m)) ` {..<M})"
definition l2 :: "(nat \<Rightarrow> complex) \<Rightarrow> real" where
  "l2 c = L2_set (\<lambda>j. cmod (c j)) {..<32}"

lemma maxQ_ge: "q \<in> Qset \<Delta> \<Longrightarrow> cmod (Fc c q) \<le> maxQ \<Delta> c"
  unfolding maxQ_def by (rule Max_ge) (simp_all add: finite_Qset)

lemma maxQ_nonneg: "Qset \<Delta> \<noteq> {} \<Longrightarrow> 0 \<le> maxQ \<Delta> c"
proof -
  assume "Qset \<Delta> \<noteq> {}"
  then obtain q where "q \<in> Qset \<Delta>" by blast
  from maxQ_ge [OF this] show ?thesis by (meson norm_ge_zero order_trans)
qed

section \<open>Lemma C.1: the certificate inequality\<close>

lemma l2_cs: "cmod (\<Sum>j<32. e j * c j) \<le> l2 e * l2 c"
proof -
  have "cmod (\<Sum>j<32. e j * c j) \<le> (\<Sum>j<32. cmod (e j * c j))" by (rule norm_sum)
  also have "\<dots> = (\<Sum>j<32. \<bar>cmod (e j)\<bar> * \<bar>cmod (c j)\<bar>)" by (simp add: norm_mult)
  also have "\<dots> \<le> L2_set (\<lambda>j. cmod (e j)) {..<32} * L2_set (\<lambda>j. cmod (c j)) {..<32}" by (rule L2_set_mult_ineq)
  finally show ?thesis unfolding l2_def .
qed

lemma cert_ineq:
  fixes \<mu> :: "nat \<Rightarrow> complex"
  assumes Qne: "Qset \<Delta> \<noteq> {}"
  shows "cmod (Fc c \<psi>) \<le> (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q)) * maxQ \<Delta> c
         + l2 (\<lambda>j. steer ucp (grid \<psi>) j - (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j)) * l2 c"
proof -
  let ?e = "\<lambda>j. steer ucp (grid \<psi>) j - (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j)"
  have "Fc c \<psi> = (\<Sum>j<32. (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j) * c j + ?e j * c j)"
    unfolding patt_def by (rule sum.cong [OF refl]) (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>j<32. (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j) * c j) + (\<Sum>j<32. ?e j * c j)"
    by (rule sum.distrib)
  also have "(\<Sum>j<32. (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j) * c j)
           = (\<Sum>j<32. \<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j * c j)" by (simp only: sum_distrib_right)
  also have "\<dots> = (\<Sum>q\<in>Qset \<Delta>. \<Sum>j<32. \<mu> q * steer ucp (grid q) j * c j)" by (rule sum.swap)
  also have "\<dots> = (\<Sum>q\<in>Qset \<Delta>. \<mu> q * Fc c q)" unfolding patt_def by (simp only: sum_distrib_left mult.assoc)
  finally have F: "Fc c \<psi> = (\<Sum>q\<in>Qset \<Delta>. \<mu> q * Fc c q) + (\<Sum>j<32. ?e j * c j)" .
  have "cmod (\<Sum>q\<in>Qset \<Delta>. \<mu> q * Fc c q) \<le> (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q) * cmod (Fc c q))"
    using norm_sum [of "\<lambda>q. \<mu> q * Fc c q" "Qset \<Delta>"] by (simp add: norm_mult)
  also have "\<dots> \<le> (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q) * maxQ \<Delta> c)"
    by (rule sum_mono) (rule mult_left_mono [OF maxQ_ge norm_ge_zero])
  also have "\<dots> = (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q)) * maxQ \<Delta> c" by (rule sum_distrib_right [symmetric])
  finally have A: "cmod (\<Sum>q\<in>Qset \<Delta>. \<mu> q * Fc c q) \<le> (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q)) * maxQ \<Delta> c" .
  have "cmod (Fc c \<psi>) \<le> cmod (\<Sum>q\<in>Qset \<Delta>. \<mu> q * Fc c q) + cmod (\<Sum>j<32. ?e j * c j)"
    unfolding F by (rule norm_triangle_ineq)
  with A l2_cs [of ?e c] show ?thesis by linarith
qed

section \<open>Lemma C.2: the sidelobes control the norm\<close>

text \<open>Real form: \<open>w = (Re c, Im c) \<in> \<real>\<^sup>6\<^sup>4\<close>; \<open>Re F = \<alpha>\<^sub>q \<cdot> w\<close>, \<open>Im F = \<beta>\<^sub>q \<cdot> w\<close>.\<close>

definition wv :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "wv c i = (if i < 32 then Re (c i) else Im (c (i - 32)))"
definition alpha :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "alpha q i = (if i < 32 then Re (steer ucp (grid q) i) else - Im (steer ucp (grid q) (i - 32)))"
definition beta :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "beta q i = (if i < 32 then Im (steer ucp (grid q) i) else Re (steer ucp (grid q) (i - 32)))"

lemma sum_64_split: "(\<Sum>i<64. f i) = (\<Sum>i<32. f i) + (\<Sum>i<32. f (i + 32))"
  for f :: "nat \<Rightarrow> 'a::comm_monoid_add"
proof -
  have "(\<Sum>i\<in>{0..<64}. f i) = (\<Sum>i\<in>{0..<32}. f i) + (\<Sum>i\<in>{32..<64}. f i)"
    by (rule sum.atLeastLessThan_concat [symmetric]) simp_all
  moreover have "(\<Sum>i\<in>{32..<64}. f i) = (\<Sum>i\<in>{0..<32}. f (i + 32))"
    using sum.shift_bounds_nat_ivl [of f 0 32 32] by simp
  ultimately show ?thesis by (simp add: atLeast0LessThan)
qed

lemma Re_Fc: "Re (Fc c q) = (\<Sum>i<64. alpha q i * wv c i)"
  unfolding patt_def Re_sum sum_64_split
  by (simp add: alpha_def wv_def sum_subtractf sum_negf)

lemma Im_Fc: "Im (Fc c q) = (\<Sum>i<64. beta q i * wv c i)"
  unfolding patt_def Im_sum sum_64_split
  by (simp add: beta_def wv_def sum.distrib)

lemma wv_norm: "(\<Sum>i<64. (wv c i)\<^sup>2) = (\<Sum>j<32. (cmod (c j))\<^sup>2)"
  unfolding sum_64_split by (simp add: wv_def cmod_power2 sum.distrib)

text \<open>The Gram matrix of the real form.\<close>
definition Gm :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "Gm \<Delta> i k = (\<Sum>q\<in>Qset \<Delta>. alpha q i * alpha q k + beta q i * beta q k)"

lemma sq_sum_sum: "(\<Sum>i<64. a i * w i)\<^sup>2 = (\<Sum>i<64. \<Sum>k<64. (a i * w i) * (a k * w k))"
  for a w :: "nat \<Rightarrow> real"
  by (simp only: power2_eq_square sum_product)

lemma quad_form: "(\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2) = (\<Sum>i<64. \<Sum>k<64. wv c i * Gm \<Delta> i k * wv c k)"
proof -
  let ?w = "wv c"
  have "(\<Sum>i<64. \<Sum>k<64. ?w i * Gm \<Delta> i k * ?w k)
      = (\<Sum>i<64. \<Sum>k<64. \<Sum>q\<in>Qset \<Delta>. ?w i * (alpha q i * alpha q k + beta q i * beta q k) * ?w k)"
    unfolding Gm_def by (simp add: sum_distrib_left sum_distrib_right)
  also have "\<dots> = (\<Sum>i<64. \<Sum>q\<in>Qset \<Delta>. \<Sum>k<64. ?w i * (alpha q i * alpha q k + beta q i * beta q k) * ?w k)"
    by (rule sum.cong [OF refl]) (rule sum.swap)
  also have "\<dots> = (\<Sum>q\<in>Qset \<Delta>. \<Sum>i<64. \<Sum>k<64. ?w i * (alpha q i * alpha q k + beta q i * beta q k) * ?w k)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2)"
  proof (rule sum.cong [OF refl])
    fix q
    have "(cmod (Fc c q))\<^sup>2 = (\<Sum>i<64. alpha q i * ?w i)\<^sup>2 + (\<Sum>i<64. beta q i * ?w i)\<^sup>2"
      unfolding cmod_power2 Re_Fc Im_Fc ..
    also have "\<dots> = (\<Sum>i<64. \<Sum>k<64. (alpha q i * ?w i) * (alpha q k * ?w k) + (beta q i * ?w i) * (beta q k * ?w k))"
      unfolding sq_sum_sum by (simp only: sum.distrib)
    also have "\<dots> = (\<Sum>i<64. \<Sum>k<64. ?w i * (alpha q i * alpha q k + beta q i * beta q k) * ?w k)"
      by (intro sum.cong [OF refl]) (simp add: algebra_simps)
    finally show "(\<Sum>i<64. \<Sum>k<64. ?w i * (alpha q i * alpha q k + beta q i * beta q k) * ?w k) = (cmod (Fc c q))\<^sup>2" ..
  qed
  finally show ?thesis ..
qed

text \<open>A real \<open>64 \<times> 64\<close> matrix \<open>Lm\<close> (lower triangular in practice, but that is not needed), a shift \<open>s2\<close>
  and the residual \<open>E = G - L L\<^sup>T - s2 I\<close>.\<close>

definition LLt :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "LLt Lm i k = (\<Sum>t<64. Lm i t * Lm k t)"

lemma LLt_psd: "0 \<le> (\<Sum>i<64. \<Sum>k<64. w i * LLt Lm i k * w k)" for w :: "nat \<Rightarrow> real"
proof -
  have "(\<Sum>i<64. \<Sum>k<64. w i * LLt Lm i k * w k) = (\<Sum>i<64. \<Sum>k<64. \<Sum>t<64. (Lm i t * w i) * (Lm k t * w k))"
    unfolding LLt_def by (intro sum.cong [OF refl]) (simp add: sum_distrib_left sum_distrib_right algebra_simps)
  also have "\<dots> = (\<Sum>i<64. \<Sum>t<64. \<Sum>k<64. (Lm i t * w i) * (Lm k t * w k))"
    by (rule sum.cong [OF refl]) (rule sum.swap)
  also have "\<dots> = (\<Sum>t<64. \<Sum>i<64. \<Sum>k<64. (Lm i t * w i) * (Lm k t * w k))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>t<64. (\<Sum>i<64. Lm i t * w i)\<^sup>2)" by (simp only: sq_sum_sum)
  also have "0 \<le> \<dots>" by (rule sum_nonneg) simp
  finally show ?thesis .
qed

lemma abs_prod_le: "\<bar>a\<bar> * \<bar>b\<bar> \<le> (a\<^sup>2 + b\<^sup>2) / 2" for a b :: real
proof -
  have "2 * (\<bar>a\<bar> * \<bar>b\<bar>) \<le> \<bar>a\<bar>\<^sup>2 + \<bar>b\<bar>\<^sup>2" using sum_squares_bound [of "\<bar>a\<bar>" "\<bar>b\<bar>"] by (simp add: mult.assoc)
  then show ?thesis by (simp add: power2_abs)
qed

lemma quad_residual:
  fixes w :: "nat \<Rightarrow> real"
  assumes row: "\<And>i. i < 64 \<Longrightarrow> (\<Sum>k<64. \<bar>E i k\<bar>) \<le> \<delta>" and col: "\<And>k. k < 64 \<Longrightarrow> (\<Sum>i<64. \<bar>E i k\<bar>) \<le> \<delta>"
  shows "\<bar>\<Sum>i<64. \<Sum>k<64. w i * E i k * w k\<bar> \<le> \<delta> * (\<Sum>i<64. (w i)\<^sup>2)"
proof -
  have "\<bar>\<Sum>i<64. \<Sum>k<64. w i * E i k * w k\<bar> \<le> (\<Sum>i<64. \<bar>\<Sum>k<64. w i * E i k * w k\<bar>)" by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>i<64. \<Sum>k<64. \<bar>w i * E i k * w k\<bar>)" by (rule sum_mono) (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w i)\<^sup>2 / 2 + \<bar>E i k\<bar> * (w k)\<^sup>2 / 2)"
  proof (intro sum_mono)
    fix i k
    have "\<bar>w i * E i k * w k\<bar> = \<bar>E i k\<bar> * (\<bar>w i\<bar> * \<bar>w k\<bar>)" by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>E i k\<bar> * (((w i)\<^sup>2 + (w k)\<^sup>2) / 2)" by (rule mult_left_mono [OF abs_prod_le abs_ge_zero])
    also have "\<dots> = \<bar>E i k\<bar> * (w i)\<^sup>2 / 2 + \<bar>E i k\<bar> * (w k)\<^sup>2 / 2" by (simp add: field_simps)
    finally show "\<bar>w i * E i k * w k\<bar> \<le> \<bar>E i k\<bar> * (w i)\<^sup>2 / 2 + \<bar>E i k\<bar> * (w k)\<^sup>2 / 2" .
  qed
  also have "\<dots> = (\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w i)\<^sup>2 / 2) + (\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w k)\<^sup>2 / 2)"
    by (simp only: sum.distrib)
  also have "\<dots> \<le> \<delta> * (\<Sum>i<64. (w i)\<^sup>2) / 2 + \<delta> * (\<Sum>i<64. (w i)\<^sup>2) / 2"
  proof (rule add_mono)
    have "(\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w i)\<^sup>2 / 2) = (\<Sum>i<64. (\<Sum>k<64. \<bar>E i k\<bar>) * (w i)\<^sup>2 / 2)"
      by (simp add: sum_distrib_right sum_divide_distrib)
    also have "\<dots> \<le> (\<Sum>i<64. \<delta> * (w i)\<^sup>2 / 2)"
      by (rule sum_mono) (simp add: row divide_right_mono mult_right_mono)
    also have "\<dots> = \<delta> * (\<Sum>i<64. (w i)\<^sup>2) / 2" by (simp add: sum_distrib_left sum_divide_distrib)
    finally show "(\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w i)\<^sup>2 / 2) \<le> \<delta> * (\<Sum>i<64. (w i)\<^sup>2) / 2" .
    have "(\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w k)\<^sup>2 / 2) = (\<Sum>k<64. \<Sum>i<64. \<bar>E i k\<bar> * (w k)\<^sup>2 / 2)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>k<64. (\<Sum>i<64. \<bar>E i k\<bar>) * (w k)\<^sup>2 / 2)" by (simp add: sum_distrib_right sum_divide_distrib)
    also have "\<dots> \<le> (\<Sum>k<64. \<delta> * (w k)\<^sup>2 / 2)"
      by (rule sum_mono) (simp add: col divide_right_mono mult_right_mono)
    also have "\<dots> = \<delta> * (\<Sum>i<64. (w i)\<^sup>2) / 2" by (simp add: sum_distrib_left sum_divide_distrib)
    finally show "(\<Sum>i<64. \<Sum>k<64. \<bar>E i k\<bar> * (w k)\<^sup>2 / 2) \<le> \<delta> * (\<Sum>i<64. (w i)\<^sup>2) / 2" .
  qed
  also have "\<dots> = \<delta> * (\<Sum>i<64. (w i)\<^sup>2)" by simp
  finally show ?thesis .
qed

lemma norm_bound:
  fixes Lm :: "nat \<Rightarrow> nat \<Rightarrow> real" and s2 \<delta> :: real and \<Delta> :: nat
  defines "E \<equiv> \<lambda>i k. Gm \<Delta> i k - LLt Lm i k - (if i = k then s2 else 0)"
  assumes row: "\<And>i. i < 64 \<Longrightarrow> (\<Sum>k<64. \<bar>E i k\<bar>) \<le> \<delta>" and col: "\<And>k. k < 64 \<Longrightarrow> (\<Sum>i<64. \<bar>E i k\<bar>) \<le> \<delta>"
  shows "(s2 - \<delta>) * (\<Sum>j<32. (cmod (c j))\<^sup>2) \<le> (\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2)"
proof -
  let ?w = "wv c"
  have G: "Gm \<Delta> i k = LLt Lm i k + (if i = k then s2 else 0) + E i k" for i k unfolding E_def by simp
  have d: "?w i * (if i = k then s2 else 0) * ?w k = (if i = k then ?w i * s2 * ?w k else 0)" for i k by simp
  have "(\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2) = (\<Sum>i<64. \<Sum>k<64. ?w i * Gm \<Delta> i k * ?w k)" by (rule quad_form)
  also have "\<dots> = (\<Sum>i<64. \<Sum>k<64. ?w i * LLt Lm i k * ?w k) + (\<Sum>i<64. \<Sum>k<64. ?w i * (if i = k then s2 else 0) * ?w k)
               + (\<Sum>i<64. \<Sum>k<64. ?w i * E i k * ?w k)"
    unfolding G by (simp add: sum.distrib algebra_simps)
  also have "(\<Sum>i<64. \<Sum>k<64. ?w i * (if i = k then s2 else 0) * ?w k) = (\<Sum>i<64. ?w i * s2 * ?w i)"
    unfolding d by (simp add: sum.delta')
  also have "\<dots> = s2 * (\<Sum>i<64. (?w i)\<^sup>2)" by (simp add: sum_distrib_left power2_eq_square mult_ac)
  finally have eq: "(\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2) = (\<Sum>i<64. \<Sum>k<64. ?w i * LLt Lm i k * ?w k) + s2 * (\<Sum>i<64. (?w i)\<^sup>2)
               + (\<Sum>i<64. \<Sum>k<64. ?w i * E i k * ?w k)" .
  have "- (\<delta> * (\<Sum>i<64. (?w i)\<^sup>2)) \<le> (\<Sum>i<64. \<Sum>k<64. ?w i * E i k * ?w k)"
    using quad_residual [OF row col, of ?w] by (simp add: abs_le_iff)
  with LLt_psd [of ?w Lm] have "(s2 - \<delta>) * (\<Sum>i<64. (?w i)\<^sup>2) \<le> (\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2)"
    unfolding eq by (simp add: algebra_simps)
  then show ?thesis unfolding wv_norm .
qed

section \<open>Theorem C.3: the floor\<close>

text \<open>A certificate for \<open>\<psi>\<close>: weights \<open>\<mu>\<close> on \<open>Q\<close> with \<open>\<Sum>|\<mu>| \<le> \<Lambda>\<close> and residual \<open>\<le> e\<close>.\<close>
definition certificate :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "certificate \<Delta> \<psi> \<mu> \<Lambda> e \<longleftrightarrow> (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q)) \<le> \<Lambda> \<and>
     (\<Sum>j<32. (cmod (steer ucp (grid \<psi>) j - (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j)))\<^sup>2) \<le> e\<^sup>2"

lemma l2_sq: "(l2 c)\<^sup>2 = (\<Sum>j<32. (cmod (c j))\<^sup>2)"
  unfolding l2_def L2_set_def by (rule real_sqrt_pow2) (rule sum_nonneg, simp)

lemma l2_sq_le: "(\<Sum>j<32. (cmod (c j))\<^sup>2) \<le> e\<^sup>2 \<Longrightarrow> 0 \<le> e \<Longrightarrow> l2 c \<le> e"
  unfolding l2_def L2_set_def by (rule real_le_lsqrt) simp_all

theorem floor_from_certificates:
  fixes Lm :: "nat \<Rightarrow> nat \<Rightarrow> real" and s2 \<delta> \<Lambda> e K :: real and \<Delta> :: nat
  defines "E \<equiv> \<lambda>i k. Gm \<Delta> i k - LLt Lm i k - (if i = k then s2 else 0)"
  assumes Qne: "Qset \<Delta> \<noteq> {}"
    and row: "\<And>i. i < 64 \<Longrightarrow> (\<Sum>k<64. \<bar>E i k\<bar>) \<le> \<delta>" and col: "\<And>k. k < 64 \<Longrightarrow> (\<Sum>i<64. \<bar>E i k\<bar>) \<le> \<delta>"
    and pos: "0 < s2 - \<delta>" and e0: "0 \<le> e" and LK: "\<Lambda> \<le> K" and K1: "1 \<le> K"
    and KK: "e\<^sup>2 * real (card (Qset \<Delta>)) \<le> (K - \<Lambda>)\<^sup>2 * (s2 - \<delta>)"
    and cert: "\<And>\<psi>. \<psi> < M \<Longrightarrow> \<psi> \<notin> Qset \<Delta> \<Longrightarrow> \<exists>\<mu>. certificate \<Delta> \<psi> \<mu> \<Lambda> e"
  shows "maxAll c \<le> K * maxQ \<Delta> c"
proof -
  let ?Q = "Qset \<Delta>" and ?n2 = "\<Sum>j<32. (cmod (c j))\<^sup>2" and ?mq = "maxQ \<Delta> c"
  have mq0: "0 \<le> ?mq" by (rule maxQ_nonneg [OF Qne])
  \<comment> \<open>the norm bound\<close>
  have "(\<Sum>q\<in>?Q. (cmod (Fc c q))\<^sup>2) \<le> (\<Sum>q\<in>?Q. ?mq\<^sup>2)"
    by (rule sum_mono) (rule power_mono [OF maxQ_ge norm_ge_zero])
  also have "\<dots> = real (card ?Q) * ?mq\<^sup>2" by simp
  finally have nb: "(s2 - \<delta>) * ?n2 \<le> real (card ?Q) * ?mq\<^sup>2"
    using norm_bound [OF row [unfolded E_def] col [unfolded E_def], of c] by linarith
  \<comment> \<open>hence \<open>e\<^sup>2 \<parallel>c\<parallel>\<^sup>2 \<le> (K - \<Lambda>)\<^sup>2 maxQ\<^sup>2\<close>\<close>
  have "(s2 - \<delta>) * (e\<^sup>2 * ?n2) = e\<^sup>2 * ((s2 - \<delta>) * ?n2)" by (simp add: mult_ac)
  also have "\<dots> \<le> e\<^sup>2 * (real (card ?Q) * ?mq\<^sup>2)" by (rule mult_left_mono [OF nb]) simp
  also have "\<dots> = (e\<^sup>2 * real (card ?Q)) * ?mq\<^sup>2" by (simp add: mult_ac)
  also have "\<dots> \<le> ((K - \<Lambda>)\<^sup>2 * (s2 - \<delta>)) * ?mq\<^sup>2" by (rule mult_right_mono [OF KK]) simp
  also have "\<dots> = (s2 - \<delta>) * ((K - \<Lambda>)\<^sup>2 * ?mq\<^sup>2)" by (simp add: mult_ac)
  finally have "e\<^sup>2 * ?n2 \<le> (K - \<Lambda>)\<^sup>2 * ?mq\<^sup>2" using pos by (simp add: mult_le_cancel_left_pos)
  hence sq: "(e * l2 c)\<^sup>2 \<le> ((K - \<Lambda>) * ?mq)\<^sup>2" by (simp add: power_mult_distrib l2_sq)
  have KL0: "0 \<le> (K - \<Lambda>) * ?mq" using LK mq0 by simp
  have el: "e * l2 c \<le> (K - \<Lambda>) * ?mq" by (rule power2_le_imp_le [OF sq KL0])
  \<comment> \<open>per grid point\<close>
  have pt: "cmod (Fc c m) \<le> K * ?mq" if "m < M" for m
  proof (cases "m \<in> ?Q")
    case True
    have "cmod (Fc c m) \<le> ?mq" by (rule maxQ_ge [OF True])
    also have "1 * ?mq \<le> K * ?mq" by (rule mult_right_mono [OF K1 mq0])
    finally show ?thesis by simp
  next
    case False
    from cert [OF that False] obtain \<mu> where c1: "(\<Sum>q\<in>?Q. cmod (\<mu> q)) \<le> \<Lambda>"
      and c2: "(\<Sum>j<32. (cmod (steer ucp (grid m) j - (\<Sum>q\<in>?Q. \<mu> q * steer ucp (grid q) j)))\<^sup>2) \<le> e\<^sup>2"
      unfolding certificate_def by blast
    let ?e = "\<lambda>j. steer ucp (grid m) j - (\<Sum>q\<in>?Q. \<mu> q * steer ucp (grid q) j)"
    have le: "l2 ?e \<le> e" by (rule l2_sq_le [OF c2 e0])
    have "cmod (Fc c m) \<le> (\<Sum>q\<in>?Q. cmod (\<mu> q)) * ?mq + l2 ?e * l2 c" by (rule cert_ineq [OF Qne])
    also have "\<dots> \<le> \<Lambda> * ?mq + e * l2 c"
      using c1 le mq0 by (intro add_mono mult_right_mono) (simp_all add: l2_def)
    also have "\<dots> \<le> \<Lambda> * ?mq + (K - \<Lambda>) * ?mq" using el by simp
    finally show ?thesis by (simp add: algebra_simps)
  qed
  have ne: "{..<M} \<noteq> {}" by (simp add: M_def lessThan_empty_iff)
  show ?thesis unfolding maxAll_def by (rule Max.boundedI) (use ne pt in auto)
qed

end
