theory Node_Enclosure
  imports Interval_Model
begin

section \<open>Curvature bounds\<close>

definition gam_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval" where
  "gam_ivl p q j = mult_float_interval p (kw_ivl p)
     (sqrt_float_interval p (plus_float_interval p (mult_float_interval p (interval_of (fst (q j))) (interval_of (fst (q j))))
                                                  (mult_float_interval p (interval_of (snd (q j))) (interval_of (snd (q j))))))"

lemma gam_in: "gam (fpos q) j \<in>\<^sub>r gam_ivl p q j"
  unfolding gam_def gam_ivl_def fpos_def power2_eq_square
  by (intro mult_float_intervalI plus_float_intervalI sqrt_float_intervalI kw_in interval_of) simp_all

text \<open>An enclosure of \<open>|z|\<close> that needs no square root: \<open>|z| \<le> |Re z| + |Im z|\<close>.\<close>
definition absr :: "nat \<Rightarrow> civ \<Rightarrow> float interval" where
  "absr p Z = Ivl 0 (upper (plus_float_interval p (abs_interval (fst Z)) (abs_interval (snd Z))))"

lemma cmod_le_abs_Re_Im: "cmod z \<le> \<bar>Re z\<bar> + \<bar>Im z\<bar>"
proof -
  have "(cmod z)\<^sup>2 = (Re z)\<^sup>2 + (Im z)\<^sup>2" by (rule cmod_power2)
  also have "\<dots> \<le> (\<bar>Re z\<bar> + \<bar>Im z\<bar>)\<^sup>2" by (simp add: power2_eq_square abs_mult_self_eq algebra_simps)
  finally show ?thesis by (rule power2_le_imp_le) simp
qed

lemma absr_in: "cin z Z \<Longrightarrow> cmod z \<in>\<^sub>r absr p Z"
proof -
  assume "cin z Z"
  then have "\<bar>Re z\<bar> + \<bar>Im z\<bar> \<in>\<^sub>r plus_float_interval p (abs_interval (fst Z)) (abs_interval (snd Z))"
    by (intro plus_float_intervalI abs_in_float_intervalI) (simp_all add: cin_def)
  then have "\<bar>Re z\<bar> + \<bar>Im z\<bar> \<le> real_of_float (upper (plus_float_interval p (abs_interval (fst Z)) (abs_interval (snd Z))))"
    by (simp add: set_of_eq)
  with cmod_le_abs_Re_Im [of z] show ?thesis
    unfolding absr_def by (intro in_real_intervalI) (simp_all add: Ivl_simps)
qed

definition fsum :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval" where
  "fsum p Xs = fold (\<lambda>X A. X + A) Xs 0"

lemma fsum_in:
  assumes "length xs = length Xs" "\<And>i. i < length xs \<Longrightarrow> xs ! i \<in>\<^sub>r Xs ! i"
  shows "sum_list xs \<in>\<^sub>r fsum p Xs"
proof -
  have "sum_list xs + a \<in>\<^sub>r fold (\<lambda>X A. X + A) Xs A"
    if "length xs = length Xs" "\<And>i. i < length xs \<Longrightarrow> xs ! i \<in>\<^sub>r Xs ! i" "a \<in>\<^sub>r A" for Xs a A
    using that
  proof (induction xs arbitrary: Xs a A)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    then obtain X Xs' where Xs: "Xs = X # Xs'" by (cases Xs) auto
    have xX: "x \<in>\<^sub>r X" using Cons.prems(2) [of 0] by (simp add: Xs)
    have 1: "x + a \<in>\<^sub>r X + A" by (intro plus_in_float_intervalI xX Cons.prems(3))
    have "sum_list xs + (x + a) \<in>\<^sub>r fold (\<lambda>X A. X + A) Xs' (X + A)"
    proof (intro Cons.IH 1)
      show "length xs = length Xs'" using Cons.prems(1) by (simp add: Xs)
      fix i assume "i < length xs"
      then show "xs ! i \<in>\<^sub>r Xs' ! i" using Cons.prems(2) [of "Suc i"] by (simp add: Xs)
    qed
    then show ?case by (simp add: Xs add.assoc add.commute add.left_commute)
  qed
  from this [of Xs 0 0] assms show ?thesis unfolding fsum_def by (simp add: zero_in_float_intervalI)
qed

text \<open>The constants \<open>B, D, E\<close> and \<open>H\<close> of Lemma 2.4 as intervals, for given interval rows \<open>R\<close>.\<close>
definition Bc_ivl :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval" where
  "Bc_ivl p N R = fsum p (map (\<lambda>j. absr p (R j)) [0..<N])"
definition Dc_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval" where
  "Dc_ivl p q N R = fsum p (map (\<lambda>j. absr p (R j) * gam_ivl p q j) [0..<N])"
definition Ec_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval" where
  "Ec_ivl p q N R = fsum p (map (\<lambda>j. absr p (R j) * (gam_ivl p q j + gam_ivl p q j * gam_ivl p q j)) [0..<N])"
definition Hc_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval" where
  "Hc_ivl p q N R = interval_of (Float 2 0) * (Dc_ivl p q N R * Dc_ivl p q N R + Bc_ivl p N R * Ec_ivl p q N R)"

lemma Bc_in: "(\<And>j. j < N \<Longrightarrow> cin (r j) (R j)) \<Longrightarrow> Bc r N \<in>\<^sub>r Bc_ivl p N R"
  unfolding Bc_def Bc_ivl_def sum_lessThan_sum_list by (intro fsum_in) (simp_all add: absr_in)

lemma Dc_in: "(\<And>j. j < N \<Longrightarrow> cin (r j) (R j)) \<Longrightarrow> Dc r (fpos q) N \<in>\<^sub>r Dc_ivl p q N R"
  unfolding Dc_def Dc_ivl_def sum_lessThan_sum_list
  by (intro fsum_in) (simp_all add: absr_in gam_in times_in_float_intervalI)

lemma Ec_in: "(\<And>j. j < N \<Longrightarrow> cin (r j) (R j)) \<Longrightarrow> Ec r (fpos q) N \<in>\<^sub>r Ec_ivl p q N R"
  unfolding Ec_def Ec_ivl_def sum_lessThan_sum_list power2_eq_square
  by (intro fsum_in) (simp_all add: absr_in gam_in times_in_float_intervalI plus_in_float_intervalI)

lemma Hc_in: "(\<And>j. j < N \<Longrightarrow> cin (r j) (R j)) \<Longrightarrow> Hc r (fpos q) N \<in>\<^sub>r Hc_ivl p q N R"
proof -
  assume a: "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)"
  have "real_of_float (Float 2 0) * (Dc r (fpos q) N * Dc r (fpos q) N + Bc r N * Ec r (fpos q) N) \<in>\<^sub>r Hc_ivl p q N R"
    unfolding Hc_ivl_def by (intro times_in_float_intervalI plus_in_float_intervalI interval_of Bc_in Dc_in Ec_in a)
  then show ?thesis by (simp add: Hc_def power2_eq_square Float.compute_float_numeral)
qed

text \<open>The same with the \<open>\<gamma>\<close> enclosures precomputed in a list (for execution).\<close>
definition gamL :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval list" where
  "gamL p q N = map (gam_ivl p q) [0..<N]"

definition Hc_ivlG :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval list \<Rightarrow> float interval" where
  "Hc_ivlG p N R GL = (let A = map (\<lambda>j. absr p (R j)) [0..<N];
       B = fsum p A;
       D = fsum p (map (\<lambda>j. A ! j * GL ! j) [0..<N]);
       E = fsum p (map (\<lambda>j. A ! j * (GL ! j + GL ! j * GL ! j)) [0..<N])
     in interval_of (Float 2 0) * (D * D + B * E))"

lemma map_upt_cong': "(\<And>j. j < n \<Longrightarrow> f j = g j) \<Longrightarrow> map f [0..<n] = map g [0..<n]"
  by (intro map_cong) auto

lemma Hc_ivlG_eq: "Hc_ivlG p N R (gamL p q N) = Hc_ivl p q N R"
proof -
  have A: "\<And>j. j < N \<Longrightarrow> map (\<lambda>j. absr p (R j)) [0..<N] ! j = absr p (R j)" by simp
  have G: "\<And>j. j < N \<Longrightarrow> map (gam_ivl p q) [0..<N] ! j = gam_ivl p q j" by simp
  show ?thesis
    unfolding Hc_ivlG_def Hc_ivl_def Bc_ivl_def Dc_ivl_def Ec_ivl_def Let_def gamL_def
    by (intro arg_cong2 [where f = "(*)"] arg_cong2 [where f = "(+)"] refl
              arg_cong [where f = "fsum p"] map_upt_cong') (simp_all add: A G)
qed

section \<open>Enclosures at the midpoint\<close>

text \<open>\<open>psi1\<close> as an interval, and the derivative factor \<open>c0' = (-psi1) *\<^sub>R (\<i> * c0)\<close>.\<close>
definition psi1_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> float interval \<Rightarrow> nat \<Rightarrow> float interval" where
  "psi1_ivl p q X j = mult_float_interval p (kw_ivl p)
     (plus_float_interval p (mult_float_interval p (- interval_of (fst (q j))) (sin_ivl p X))
                            (mult_float_interval p (interval_of (snd (q j))) (cos_float_interval p X)))"

lemma psi1_in: "x \<in>\<^sub>r X \<Longrightarrow> psi1 (fpos q) j x \<in>\<^sub>r psi1_ivl p q X j"
  unfolding psi1_ivl_def psi1_def fpos_def
  by (intro mult_float_intervalI plus_float_intervalI kw_in interval_of cos_float_intervalI sin_in
            uminus_in_float_intervalI) simp_all

definition imul :: "civ \<Rightarrow> civ" where "imul Z = (- snd Z, fst Z)"

lemma cin_imul: "cin z Z \<Longrightarrow> cin (\<i> * z) (imul Z)"
  by (auto simp: cin_def imul_def intro!: uminus_in_float_intervalI)

text \<open>The pattern \<open>F\<close>, its derivative \<open>F'\<close>, \<open>S = |F|\<^sup>2\<close> and \<open>S' = 2 inner F F'\<close> at a focus enclosed by \<open>X\<close>.\<close>
definition FF_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval \<Rightarrow> civ" where
  "FF_ivl p q N R X = csum p (map (\<lambda>j. cmul p (R j) (c0_ivl p q X j)) [0..<N])"

definition FF1_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval \<Rightarrow> civ" where
  "FF1_ivl p q N R X = csum p (map (\<lambda>j. cmul p (R j) (cscale p (- psi1_ivl p q X j) (imul (c0_ivl p q X j)))) [0..<N])"

definition inner_ivl :: "nat \<Rightarrow> civ \<Rightarrow> civ \<Rightarrow> float interval" where
  "inner_ivl p Z W = fst Z * fst W + snd Z * snd W"

lemma inner_in: "cin z Z \<Longrightarrow> cin w W \<Longrightarrow> inner z w \<in>\<^sub>r inner_ivl p Z W"
  unfolding inner_ivl_def inner_complex_def cin_def by (intro plus_in_float_intervalI times_in_float_intervalI) simp_all

definition SS_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval \<Rightarrow> float interval" where
  "SS_ivl p q N R X = cnorm2 p (FF_ivl p q N R X)"

definition SS1_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> civ) \<Rightarrow> float interval \<Rightarrow> float interval" where
  "SS1_ivl p q N R X = interval_of (Float 2 0) * inner_ivl p (FF_ivl p q N R X) (FF1_ivl p q N R X)"

lemma FF_in:
  assumes "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)" "x \<in>\<^sub>r X"
  shows "cin (FF r (fpos q) N x) (FF_ivl p q N R X)"
  unfolding FF_c0 FF_ivl_def sum_lessThan_sum_list
  by (intro cin_sum) (simp_all add: cin_mul cin_c0 assms)

lemma FF1_in:
  assumes "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)" "x \<in>\<^sub>r X"
  shows "cin (FF1 r (fpos q) N x) (FF1_ivl p q N R X)"
proof -
  have "FF1 r (fpos q) N x = (\<Sum>j<N. r j * ((- psi1 (fpos q) j x) *\<^sub>R (\<i> * c0 (fpos q) x j)))"
    by (simp add: FF1_def c0_cis)
  also have "cin \<dots> (FF1_ivl p q N R X)"
    unfolding FF1_ivl_def sum_lessThan_sum_list
  proof (intro cin_sum)
    fix i assume "i < length (map (\<lambda>j. r j * ((- psi1 (fpos q) j x) *\<^sub>R (\<i> * c0 (fpos q) x j))) [0..<N])"
    then have i: "i < N" by simp
    have "cin (r i * ((- psi1 (fpos q) i x) *\<^sub>R (\<i> * c0 (fpos q) x i)))
              (cmul p (R i) (cscale p (- psi1_ivl p q X i) (imul (c0_ivl p q X i))))"
      by (intro cin_mul cin_scale cin_imul cin_c0 uminus_in_float_intervalI psi1_in assms i)
    then show "cin (map (\<lambda>j. r j * ((- psi1 (fpos q) j x) *\<^sub>R (\<i> * c0 (fpos q) x j))) [0..<N] ! i)
                   (map (\<lambda>j. cmul p (R j) (cscale p (- psi1_ivl p q X j) (imul (c0_ivl p q X j)))) [0..<N] ! i)"
      using i by (simp only: nth_map length_upt nth_upt add_0 diff_zero)
  qed simp
  finally show ?thesis .
qed

lemma SS_in:
  assumes "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)" "x \<in>\<^sub>r X"
  shows "SS r (fpos q) N x \<in>\<^sub>r SS_ivl p q N R X"
  unfolding SS_def SS_ivl_def by (intro cin_norm2 FF_in assms)

lemma SS1_in:
  assumes "\<And>j. j < N \<Longrightarrow> cin (r j) (R j)" "x \<in>\<^sub>r X"
  shows "SS1 r (fpos q) N x \<in>\<^sub>r SS1_ivl p q N R X"
proof -
  have "real_of_float (Float 2 0) * inner (FF r (fpos q) N x) (FF1 r (fpos q) N x) \<in>\<^sub>r SS1_ivl p q N R X"
    unfolding SS1_ivl_def by (intro times_in_float_intervalI interval_of inner_in FF_in FF1_in assms)
  then show ?thesis by (simp add: SS1_def Float.compute_float_numeral)
qed

section \<open>Bounds over a whole interval of focus angles (E2, E3)\<close>

text \<open>For a sector \<open>[lo, hi]\<close> of floats, \<open>tc\<close> is the midpoint and \<open>h\<close> the half-width, both exact floats.\<close>
definition tc :: "float \<Rightarrow> float \<Rightarrow> float" where "tc lo hi = (lo + hi) * Float 1 (-1)"
definition hw :: "float \<Rightarrow> float \<Rightarrow> float" where "hw lo hi = (hi - lo) * Float 1 (-1)"

lemma tc_hw_cover: "real_of_float lo \<le> t \<Longrightarrow> t \<le> real_of_float hi \<Longrightarrow> \<bar>t - tc lo hi\<bar> \<le> hw lo hi"
  by (simp add: tc_def hw_def Float.compute_float_numeral abs_le_iff) (simp add: field_simps)

text \<open>The radius \<open>|S'(tc)| h + H h\<^sup>2/2\<close>, computed from an upper bound \<open>Hb\<close> on \<open>H\<close>.\<close>
definition radius_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float interval" where
  "radius_ivl p S1 Hb h = abs_interval S1 * interval_of h
     + interval_of (Float 1 (-1)) * (interval_of Hb * (interval_of h * interval_of h))"

lemma radius_bound:
  assumes "s1 \<in>\<^sub>r S1" "K \<le> real_of_float Hb" "0 \<le> K" "0 \<le> real_of_float h"
  shows "\<bar>s1\<bar> * h + K / 2 * h\<^sup>2 \<le> upper (radius_ivl p S1 Hb h)"
proof -
  have "\<bar>s1\<bar> * real_of_float h + real_of_float (Float 1 (-1)) * (real_of_float Hb * (real_of_float h * real_of_float h))
          \<in>\<^sub>r radius_ivl p S1 Hb h"
    unfolding radius_ivl_def
    by (intro plus_in_float_intervalI times_in_float_intervalI abs_in_float_intervalI interval_of assms)
  then have "\<bar>s1\<bar> * real_of_float h + real_of_float (Float 1 (-1)) * (real_of_float Hb * (real_of_float h * real_of_float h))
          \<le> upper (radius_ivl p S1 Hb h)"
    by (simp add: set_of_eq)
  moreover have "K / 2 * h\<^sup>2 \<le> real_of_float (Float 1 (-1)) * (real_of_float Hb * (real_of_float h * real_of_float h))"
    using assms(2,4) by (simp add: Float.compute_float_numeral power2_eq_square) (intro mult_right_mono mult_nonneg_nonneg; simp)
  ultimately show ?thesis by linarith
qed

end
