theory Sector_Bounds
  imports Node_Enclosure
begin

section \<open>Bounds on the squared pattern over a sector (E2)\<close>

text \<open>A node has a sector \<open>[lo, hi]\<close> of floats (radians), interval rows \<open>R\<close> (one function per grid index)
  and, per index, a float upper bound \<open>Hb\<close> on the curvature constant.\<close>

definition rad :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "rad p q N R Hb lo hi = upper (radius_ivl p (SS1_ivl p q N R (interval_of (tc lo hi))) Hb (hw lo hi))"

definition lo_b :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "lo_b p q N R Hb lo hi = lower (SS_ivl p q N R (interval_of (tc lo hi))) - rad p q N R Hb lo hi"

definition up_b :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "up_b p q N R Hb lo hi = upper (SS_ivl p q N R (interval_of (tc lo hi))) + rad p q N R Hb lo hi"

lemma Hc_nonneg: "0 \<le> Hc r (fpos q) N"
  unfolding Hc_def Bc_def Dc_def Ec_def gam_def
  by (intro mult_nonneg_nonneg add_nonneg_nonneg sum_nonneg zero_le_power2 norm_ge_zero) (simp_all add: kw_pos less_imp_le)

lemma hw_nonneg: "lo \<le> hi \<Longrightarrow> 0 \<le> real_of_float (hw lo hi)"
  by (simp add: hw_def Float.compute_float_numeral)

lemma sq_le_of_abs_le: "\<bar>a\<bar> \<le> b \<Longrightarrow> a\<^sup>2 \<le> b\<^sup>2" for a b :: real
  by (metis power2_abs power_mono abs_ge_zero)

lemma SS_sector:
  assumes R: "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)" and H: "Hc r (fpos q) N \<le> real_of_float Hb"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "real_of_float (lo_b p q N R Hb lo hi) \<le> SS r (fpos q) N t"
    and "SS r (fpos q) N t \<le> real_of_float (up_b p q N R Hb lo hi)"
proof -
  have tc_in: "real_of_float (tc lo hi) \<in>\<^sub>r interval_of (tc lo hi)" by (rule interval_of)
  have dev: "\<bar>t - tc lo hi\<bar> \<le> hw lo hi" by (rule tc_hw_cover [OF t])
  have h0: "0 \<le> real_of_float (hw lo hi)" using t by (intro hw_nonneg) simp
  have tay: "\<bar>SS r (fpos q) N t - SS r (fpos q) N (tc lo hi)\<bar>
             \<le> \<bar>SS1 r (fpos q) N (tc lo hi)\<bar> * \<bar>t - tc lo hi\<bar> + Hc r (fpos q) N / 2 * (t - tc lo hi)\<^sup>2"
    by (rule SS_taylor)
  also have "\<dots> \<le> \<bar>SS1 r (fpos q) N (tc lo hi)\<bar> * hw lo hi + Hc r (fpos q) N / 2 * (hw lo hi)\<^sup>2"
    using dev sq_le_of_abs_le [OF dev] Hc_nonneg [of r q N] abs_ge_zero [of "t - tc lo hi"]
    by (intro add_mono mult_left_mono divide_nonneg_nonneg) simp_all
  also have "\<dots> \<le> rad p q N R Hb lo hi"
    unfolding rad_def by (intro radius_bound SS1_in R tc_in H Hc_nonneg h0)
  finally have bnd: "\<bar>SS r (fpos q) N t - SS r (fpos q) N (tc lo hi)\<bar> \<le> rad p q N R Hb lo hi" .
  have mid: "SS r (fpos q) N (tc lo hi) \<in>\<^sub>r SS_ivl p q N R (interval_of (tc lo hi))"
    by (intro SS_in R tc_in)
  then have "lower (SS_ivl p q N R (interval_of (tc lo hi))) \<le> SS r (fpos q) N (tc lo hi)"
            "SS r (fpos q) N (tc lo hi) \<le> upper (SS_ivl p q N R (interval_of (tc lo hi)))"
    by (simp_all add: set_of_eq)
  then have low: "lower (SS_ivl p q N R (interval_of (tc lo hi))) \<le> SS r (fpos q) N (tc lo hi)"
       and upp: "SS r (fpos q) N (tc lo hi) \<le> upper (SS_ivl p q N R (interval_of (tc lo hi)))" .
  from bnd have b1: "SS r (fpos q) N t - SS r (fpos q) N (tc lo hi) \<le> rad p q N R Hb lo hi"
               and b2: "SS r (fpos q) N (tc lo hi) - SS r (fpos q) N t \<le> rad p q N R Hb lo hi"
    by (simp_all add: abs_le_iff)
  show "real_of_float (lo_b p q N R Hb lo hi) \<le> SS r (fpos q) N t"
    unfolding lo_b_def minus_float.rep_eq using low b2 by linarith
  show "SS r (fpos q) N t \<le> real_of_float (up_b p q N R Hb lo hi)"
    unfolding up_b_def plus_float.rep_eq using upp b1 by linarith
qed

section \<open>Bounds on neighbour differences over a sector (E3)\<close>

definition rad2 :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "rad2 p q N R R' Hb Hb' lo hi = upper (radius_ivl p
      (SS1_ivl p q N R (interval_of (tc lo hi)) - SS1_ivl p q N R' (interval_of (tc lo hi))) (Hb + Hb') (hw lo hi))"

text \<open>The enclosure of \<open>S\<^sub>m(t) - S\<^sub>m\<^sub>'(t)\<close> for all \<open>t\<close> in the sector.\<close>
definition diff_b :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float interval" where
  "diff_b p q N R R' Hb Hb' lo hi =
     (SS_ivl p q N R (interval_of (tc lo hi)) - SS_ivl p q N R' (interval_of (tc lo hi)))
     + Ivl (- rad2 p q N R R' Hb Hb' lo hi) (rad2 p q N R R' Hb Hb' lo hi)"

lemma SS_diff_sector:
  assumes R: "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)" and R': "\<And>j. j < N \<Longrightarrow> cin (r' j) (R' j)"
    and H: "Hc r (fpos q) N \<le> real_of_float Hb" and H': "Hc r' (fpos q) N \<le> real_of_float Hb'"
    and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "SS r (fpos q) N t - SS r' (fpos q) N t \<in>\<^sub>r diff_b p q N R R' Hb Hb' lo hi"
proof -
  let ?c = "real_of_float (tc lo hi)"
  have tc_in: "?c \<in>\<^sub>r interval_of (tc lo hi)" by (rule interval_of)
  have dev: "\<bar>t - tc lo hi\<bar> \<le> hw lo hi" by (rule tc_hw_cover [OF t])
  have h0: "0 \<le> real_of_float (hw lo hi)" using t by (intro hw_nonneg) simp
  have K0: "0 \<le> Hc r (fpos q) N + Hc r' (fpos q) N" using Hc_nonneg by (meson add_nonneg_nonneg)
  have "\<bar>(SS r (fpos q) N t - SS r' (fpos q) N t) - (SS r (fpos q) N ?c - SS r' (fpos q) N ?c)\<bar>
        \<le> \<bar>SS1 r (fpos q) N ?c - SS1 r' (fpos q) N ?c\<bar> * \<bar>t - ?c\<bar> + (Hc r (fpos q) N + Hc r' (fpos q) N) / 2 * (t - ?c)\<^sup>2"
    by (rule SS_diff_taylor)
  also have "\<dots> \<le> \<bar>SS1 r (fpos q) N ?c - SS1 r' (fpos q) N ?c\<bar> * hw lo hi + (Hc r (fpos q) N + Hc r' (fpos q) N) / 2 * (hw lo hi)\<^sup>2"
    using dev sq_le_of_abs_le [OF dev] K0 abs_ge_zero [of "t - ?c"]
    by (intro add_mono mult_left_mono divide_nonneg_nonneg) simp_all
  also have "\<dots> \<le> rad2 p q N R R' Hb Hb' lo hi"
    unfolding rad2_def
  proof (intro radius_bound K0 h0)
    show "SS1 r (fpos q) N ?c - SS1 r' (fpos q) N ?c \<in>\<^sub>r SS1_ivl p q N R (interval_of (tc lo hi)) - SS1_ivl p q N R' (interval_of (tc lo hi))"
      by (intro minus_in_float_intervalI SS1_in R R' tc_in)
    show "Hc r (fpos q) N + Hc r' (fpos q) N \<le> real_of_float (Hb + Hb')" using H H' by simp
  qed
  finally have bnd: "\<bar>(SS r (fpos q) N t - SS r' (fpos q) N t) - (SS r (fpos q) N ?c - SS r' (fpos q) N ?c)\<bar>
                     \<le> rad2 p q N R R' Hb Hb' lo hi" .
  have mid: "SS r (fpos q) N ?c - SS r' (fpos q) N ?c \<in>\<^sub>r SS_ivl p q N R (interval_of (tc lo hi)) - SS_ivl p q N R' (interval_of (tc lo hi))"
    by (intro minus_in_float_intervalI SS_in R R' tc_in)
  have "(SS r (fpos q) N t - SS r' (fpos q) N t) - (SS r (fpos q) N ?c - SS r' (fpos q) N ?c)
        \<in>\<^sub>r Ivl (- rad2 p q N R R' Hb Hb' lo hi) (rad2 p q N R R' Hb Hb' lo hi)"
    using bnd by (intro in_real_intervalI) (simp_all add: Ivl_simps abs_le_iff)
  from plus_in_float_intervalI [OF mid this] show ?thesis unfolding diff_b_def by simp
qed

section \<open>The circular distance over a sector (E4)\<close>

definition twopi_ivl :: "nat \<Rightarrow> float interval" where
  "twopi_ivl p = mult_float_interval p (interval_of (Float 2 0)) (pi_ivl p)"

lemma twopi_in: "2 * pi \<in>\<^sub>r twopi_ivl p"
  unfolding twopi_ivl_def using mult_float_intervalI [OF interval_of pi_in, of "Float 2 0" p]
  by (simp add: Float.compute_float_numeral)

text \<open>If \<open>|w| \<le> 2\<pi>\<close> for \<open>w = x - 2\<pi>n\<close>, the circular distance is the smallest of \<open>|w|, |w - 2\<pi>|, |w + 2\<pi>|\<close>.\<close>
lemma cdist_three:
  assumes "\<bar>(a - b) - 2 * pi * of_int n\<bar> \<le> 2 * pi"
  shows "cdist a b = min \<bar>(a - b) - 2 * pi * of_int n\<bar>
                       (min \<bar>(a - b) - 2 * pi * of_int n - 2 * pi\<bar> \<bar>(a - b) - 2 * pi * of_int n + 2 * pi\<bar>)"
proof -
  define x where "x = a - b"
  define r where "r = round (x / (2 * pi))"
  have cd: "cdist a b = \<bar>x - 2 * pi * of_int r\<bar>" by (simp add: cdist_def x_def r_def)
  have le1: "cdist a b \<le> \<bar>x - 2 * pi * of_int n\<bar>" unfolding x_def by (rule cdist_min)
  have le2: "cdist a b \<le> \<bar>x - 2 * pi * of_int n - 2 * pi\<bar>"
    using cdist_min [of a b "n + 1"] by (simp add: x_def algebra_simps)
  have le3: "cdist a b \<le> \<bar>x - 2 * pi * of_int n + 2 * pi\<bar>"
    using cdist_min [of a b "n - 1"] by (simp add: x_def algebra_simps)
  have "\<bar>x / (2 * pi) - of_int n\<bar> \<le> 1"
  proof -
    have "2 * pi * \<bar>x / (2 * pi) - of_int n\<bar> = \<bar>x - 2 * pi * of_int n\<bar>" by (rule two_pi_abs)
    with assms have "2 * pi * \<bar>x / (2 * pi) - of_int n\<bar> \<le> 2 * pi * 1" by (simp add: x_def)
    then show ?thesis using pi_gt_zero by (simp add: mult_le_cancel_left_pos)
  qed
  moreover have "\<bar>x / (2 * pi) - of_int r\<bar> \<le> 1 / 2"
    unfolding r_def using of_int_round_abs_le [of "x / (2 * pi)"] by (simp add: abs_minus_commute)
  ultimately have "\<bar>of_int r - of_int n\<bar> \<le> (3::real) / 2" by linarith
  then have "real_of_int \<bar>r - n\<bar> < real_of_int 2" by (simp only: of_int_abs of_int_diff; linarith)
  then have "\<bar>r - n\<bar> < 2" using of_int_less_iff by blast
  then have cases: "r = n \<or> r = n + 1 \<or> r = n - 1" by auto
  have mem: "cdist a b = \<bar>x - 2 * pi * of_int n\<bar> \<or> cdist a b = \<bar>x - 2 * pi * of_int n - 2 * pi\<bar>
             \<or> cdist a b = \<bar>x - 2 * pi * of_int n + 2 * pi\<bar>"
    using cases cd by (auto simp: algebra_simps)
  have ge: "min \<bar>x - 2 * pi * of_int n\<bar> (min \<bar>x - 2 * pi * of_int n - 2 * pi\<bar> \<bar>x - 2 * pi * of_int n + 2 * pi\<bar>) \<le> cdist a b"
    using mem by (auto simp: min_le_iff_disj)
  have le: "cdist a b \<le> min \<bar>x - 2 * pi * of_int n\<bar> (min \<bar>x - 2 * pi * of_int n - 2 * pi\<bar> \<bar>x - 2 * pi * of_int n + 2 * pi\<bar>)"
    using le1 le2 le3 by simp
  from antisym [OF le ge] show ?thesis by (simp add: x_def)
qed

text \<open>The interval version: \<open>G\<close> encloses the grid angle, \<open>c\<close> is the (float) midpoint, \<open>n\<close> any integer.\<close>
definition w_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> int \<Rightarrow> float interval" where
  "w_ivl p G c n = (G - interval_of c) - interval_of (Float n 0) * twopi_ivl p"

definition cd_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> int \<Rightarrow> float interval" where
  "cd_ivl p G c n = min_interval (abs_interval (w_ivl p G c n))
     (min_interval (abs_interval (w_ivl p G c n - twopi_ivl p)) (abs_interval (w_ivl p G c n + twopi_ivl p)))"

lemma w_in: "a \<in>\<^sub>r G \<Longrightarrow> (a - real_of_float c) - 2 * pi * of_int n \<in>\<^sub>r w_ivl p G c n"
  unfolding w_ivl_def
  using minus_in_float_intervalI [OF minus_in_float_intervalI [OF _ interval_of] times_in_float_intervalI [OF interval_of twopi_in], of a G c "Float n 0" p]
  by (simp add: Float.compute_float_numeral mult.commute)

lemma min_in_float: "a \<in>\<^sub>r A \<Longrightarrow> b \<in>\<^sub>r B \<Longrightarrow> min a b \<in>\<^sub>r min_interval A B"
  by (simp add: min_intervalI)

lemma in_real_upper: "x \<in>\<^sub>r X \<Longrightarrow> x \<le> real_of_float (upper X)"
  by (simp add: set_of_eq)

lemma in_real_lower: "x \<in>\<^sub>r X \<Longrightarrow> real_of_float (lower X) \<le> x"
  by (simp add: set_of_eq)

lemma cd_in:
  assumes aG: "a \<in>\<^sub>r G" and small: "upper (abs_interval (w_ivl p G c n)) \<le> lower (twopi_ivl p)"
  shows "cdist a (real_of_float c) \<in>\<^sub>r cd_ivl p G c n"
proof -
  let ?w = "(a - real_of_float c) - 2 * pi * of_int n"
  have wW: "?w \<in>\<^sub>r w_ivl p G c n" by (rule w_in [OF aG])
  have "\<bar>?w\<bar> \<le> real_of_float (upper (abs_interval (w_ivl p G c n)))"
    by (rule in_real_upper [OF abs_in_float_intervalI [OF wW]])
  also have "\<dots> \<le> real_of_float (lower (twopi_ivl p))" using small unfolding less_eq_float.rep_eq .
  also have "\<dots> \<le> 2 * pi" by (rule in_real_lower [OF twopi_in])
  finally have "cdist a (real_of_float c) = min \<bar>?w\<bar> (min \<bar>?w - 2 * pi\<bar> \<bar>?w + 2 * pi\<bar>)"
    by (rule cdist_three)
  also have "\<dots> \<in>\<^sub>r cd_ivl p G c n"
    unfolding cd_ivl_def
    by (intro min_in_float abs_in_float_intervalI wW minus_in_float_intervalI plus_in_float_intervalI twopi_in)
  finally show ?thesis .
qed

text \<open>Distance bounds for every focus in the sector (Lemma 2.5).\<close>
definition dmin_b :: "float interval \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "dmin_b CD lo hi = lower CD - hw lo hi"
definition dmax_b :: "float interval \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" where
  "dmax_b CD lo hi = upper CD + hw lo hi"

lemma dist_sector:
  assumes cd: "cdist a (real_of_float (tc lo hi)) \<in>\<^sub>r CD" and t: "real_of_float lo \<le> t" "t \<le> real_of_float hi"
  shows "real_of_float (dmin_b CD lo hi) \<le> cdist a t" "cdist a t \<le> real_of_float (dmax_b CD lo hi)"
proof -
  have lip: "\<bar>cdist a t - cdist a (tc lo hi)\<bar> \<le> \<bar>t - tc lo hi\<bar>" by (rule cdist_lipschitz)
  have dev: "\<bar>t - tc lo hi\<bar> \<le> hw lo hi" by (rule tc_hw_cover [OF t])
  have low: "lower CD \<le> cdist a (tc lo hi)" and upp: "cdist a (tc lo hi) \<le> upper CD"
    using in_real_lower [OF cd] in_real_upper [OF cd] by simp_all
  have b1: "cdist a t - cdist a (tc lo hi) \<le> hw lo hi"
    using conjunct1 [OF lip [unfolded abs_le_iff]] dev by linarith
  have b2: "cdist a (tc lo hi) - cdist a t \<le> hw lo hi"
    using conjunct2 [OF lip [unfolded abs_le_iff]] dev by linarith
  show "real_of_float (dmin_b CD lo hi) \<le> cdist a t" unfolding dmin_b_def minus_float.rep_eq using low b2 by linarith
  show "cdist a t \<le> real_of_float (dmax_b CD lo hi)" unfolding dmax_b_def plus_float.rep_eq using upp b1 by linarith
qed

end
