theory Taylor_Enclosure
  imports Perturbative_Basics
begin

section \<open>A second-order Taylor bound\<close>

text \<open>If \<open>f\<close> is twice differentiable with \<open>|f''| \<le> K\<close> everywhere, then
  \<open>|f x - f c| \<le> |f' c| |x - c| + K/2 (x - c)\<^sup>2\<close>.  This is Taylor's theorem with the
  Lagrange remainder, \<open>n = 2\<close>.\<close>

lemma taylor2_bound:
  fixes f f1 f2 :: "real \<Rightarrow> real"
  assumes d1: "\<And>t. DERIV f t :> f1 t" and d2: "\<And>t. DERIV f1 t :> f2 t"
    and K: "\<And>t. \<bar>f2 t\<bar> \<le> K"
  shows "\<bar>f x - f c\<bar> \<le> \<bar>f1 c\<bar> * \<bar>x - c\<bar> + K / 2 * (x - c)\<^sup>2"
proof (cases "x = c")
  case True
  then show ?thesis by simp
next
  case False
  define diff where "diff = (\<lambda>m. [f, f1, f2] ! m)"
  have "diff 0 = f" by (simp add: diff_def)
  moreover have "\<forall>m t. m < 2 \<and> min x c \<le> t \<and> t \<le> max x c \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  proof (intro allI impI)
    fix m :: nat and t :: real assume "m < 2 \<and> min x c \<le> t \<and> t \<le> max x c"
    then have "m = 0 \<or> m = 1" by auto
    then show "DERIV (diff m) t :> diff (Suc m) t"
      using d1 d2 by (auto simp: diff_def)
  qed
  ultimately obtain t where t: "f x = (\<Sum>m<2. diff m c / fact m * (x - c) ^ m) + diff 2 t / fact 2 * (x - c) ^ 2"
    using Taylor [of 2 diff f "min x c" "max x c" c x] False by auto
  have "(\<Sum>m<2. diff m c / fact m * (x - c) ^ m) = f c + f1 c * (x - c)"
    by (simp add: diff_def numeral_2_eq_2)
  with t have "f x - f c = f1 c * (x - c) + f2 t / 2 * (x - c)\<^sup>2"
    by (simp add: diff_def)
  then have "\<bar>f x - f c\<bar> \<le> \<bar>f1 c * (x - c)\<bar> + \<bar>f2 t / 2 * (x - c)\<^sup>2\<bar>"
    by (metis abs_triangle_ineq)
  also have "\<bar>f2 t / 2 * (x - c)\<^sup>2\<bar> = \<bar>f2 t\<bar> / 2 * (x - c)\<^sup>2"
    by (simp add: abs_mult abs_divide)
  also have "\<dots> \<le> K / 2 * (x - c)\<^sup>2"
    using K [of t] by (intro mult_right_mono) auto
  finally show ?thesis by (simp add: abs_mult)
qed

section \<open>Derivatives of the initial excitation\<close>

definition psi :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "psi p j t = kw * (fst (p j) * cos t + snd (p j) * sin t)"

definition psi1 :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "psi1 p j t = kw * (- fst (p j) * sin t + snd (p j) * cos t)"

definition gam :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "gam p j = kw * sqrt ((fst (p j))\<^sup>2 + (snd (p j))\<^sup>2)"

lemma kw_pos: "kw > 0"
  by (simp add: kw_def)

lemma DERIV_psi: "DERIV (psi p j) t :> psi1 p j t"
  unfolding psi_def psi1_def by (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma DERIV_psi1: "DERIV (psi1 p j) t :> - psi p j t"
  unfolding psi_def psi1_def by (auto intro!: derivative_eq_intros simp: algebra_simps)

text \<open>Cauchy--Schwarz in the plane: \<open>(x cos t + y sin t)\<^sup>2 \<le> x\<^sup>2 + y\<^sup>2\<close>.\<close>
lemma plane_cs: "(x * cos t + y * sin t)\<^sup>2 \<le> x\<^sup>2 + y\<^sup>2" for x y t :: real
proof -
  have "(x * cos t + y * sin t)\<^sup>2 + (- x * sin t + y * cos t)\<^sup>2 = (x\<^sup>2 + y\<^sup>2) * ((cos t)\<^sup>2 + (sin t)\<^sup>2)"
    unfolding power2_eq_square by algebra
  then have "(x * cos t + y * sin t)\<^sup>2 + (- x * sin t + y * cos t)\<^sup>2 = x\<^sup>2 + y\<^sup>2"
    by (simp only: sin_cos_squared_add2 mult_1_right)
  then show ?thesis using zero_le_power2 [of "- x * sin t + y * cos t"] by linarith
qed

lemma abs_le_sqrt: "a\<^sup>2 \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> sqrt b"
  by (metis real_sqrt_abs real_sqrt_le_mono)

lemma psi_bound: "\<bar>psi p j t\<bar> \<le> gam p j"
proof -
  have "\<bar>fst (p j) * cos t + snd (p j) * sin t\<bar> \<le> sqrt ((fst (p j))\<^sup>2 + (snd (p j))\<^sup>2)"
    by (rule abs_le_sqrt [OF plane_cs])
  then show ?thesis
    unfolding psi_def gam_def abs_mult abs_of_pos [OF kw_pos] using kw_pos by (intro mult_left_mono) simp_all
qed

lemma psi1_bound: "\<bar>psi1 p j t\<bar> \<le> gam p j"
proof -
  have "(- fst (p j) * sin t + snd (p j) * cos t)\<^sup>2 \<le> (fst (p j))\<^sup>2 + (snd (p j))\<^sup>2"
    using plane_cs [of "snd (p j)" t "- fst (p j)"] by (simp add: algebra_simps)
  then have "\<bar>- fst (p j) * sin t + snd (p j) * cos t\<bar> \<le> sqrt ((fst (p j))\<^sup>2 + (snd (p j))\<^sup>2)"
    by (rule abs_le_sqrt)
  then show ?thesis
    unfolding psi1_def gam_def abs_mult abs_of_pos [OF kw_pos] using kw_pos by (intro mult_left_mono) simp_all
qed

lemma c0_cis: "c0 p t j = cis (- psi p j t)"
  by (simp add: c0_def steer_def psi_def cis_cnj)

lemma has_vector_derivative_cis_psi:
  "((\<lambda>t. cis (- psi p j t)) has_vector_derivative ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) (at t)"
proof -
  have "((\<lambda>t. - psi p j t) has_derivative (*) (- psi1 p j t)) (at t)"
    using DERIV_minus [OF DERIV_psi [of p j t]] unfolding has_field_derivative_def .
  from has_derivative_cis [OF this] show ?thesis
    unfolding has_vector_derivative_def by (simp add: scaleR_scaleR mult.commute)
qed

section \<open>The pattern as a function of the focus, and its first two derivatives\<close>

definition FF :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex" where
  "FF r p N t = (\<Sum>j<N. r j * cis (- psi p j t))"

definition FF1 :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex" where
  "FF1 r p N t = (\<Sum>j<N. r j * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t))))"

definition FF2 :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> complex" where
  "FF2 r p N t = (\<Sum>j<N. r j * ((- psi1 p j t) *\<^sub>R (\<i> * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t))))
                              + psi p j t *\<^sub>R (\<i> * cis (- psi p j t))))"

lemma FF_c0: "FF r p N t = (\<Sum>j<N. r j * c0 p t j)"
  by (simp add: FF_def c0_cis)

lemma FF_deriv: "(FF r p N has_vector_derivative FF1 r p N t) (at t)"
  unfolding FF_def FF1_def
  by (intro derivative_intros has_vector_derivative_cis_psi)

lemma FF1_deriv: "(FF1 r p N has_vector_derivative FF2 r p N t) (at t)"
  unfolding FF1_def FF2_def
proof (rule has_vector_derivative_sum, rule has_vector_derivative_mult_right)
  fix j
  have f: "((\<lambda>t. - psi1 p j t) has_field_derivative psi p j t) (at t)"
    using DERIV_minus [OF DERIV_psi1 [of p j t]] by simp
  have g: "((\<lambda>t. \<i> * cis (- psi p j t)) has_vector_derivative \<i> * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) (at t)"
    by (rule has_vector_derivative_mult_right [OF has_vector_derivative_cis_psi])
  show "((\<lambda>t. (- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t))) has_vector_derivative
          (- psi1 p j t) *\<^sub>R (\<i> * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) + psi p j t *\<^sub>R (\<i> * cis (- psi p j t))) (at t)"
    by (rule has_vector_derivative_scaleR [OF f g])
qed

text \<open>The constants of Lemma 2.4.\<close>
definition Bc :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where "Bc r N = (\<Sum>j<N. cmod (r j))"
definition Dc :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Dc r p N = (\<Sum>j<N. cmod (r j) * gam p j)"
definition Ec :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Ec r p N = (\<Sum>j<N. cmod (r j) * (gam p j + (gam p j)\<^sup>2))"
definition Hc :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Hc r p N = 2 * ((Dc r p N)\<^sup>2 + Bc r N * Ec r p N)"

lemma norm_FF: "cmod (FF r p N t) \<le> Bc r N"
  unfolding FF_def Bc_def by (rule order_trans [OF norm_sum]) (simp add: norm_mult)

lemma norm_FF1: "cmod (FF1 r p N t) \<le> Dc r p N"
  unfolding FF1_def Dc_def
proof (rule order_trans [OF norm_sum], rule sum_mono)
  fix j
  have "cmod (r j * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) = cmod (r j) * \<bar>psi1 p j t\<bar>"
    by (simp add: norm_mult)
  also have "\<dots> \<le> cmod (r j) * gam p j"
    by (intro mult_left_mono psi1_bound) simp
  finally show "cmod (r j * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) \<le> cmod (r j) * gam p j" .
qed

lemma norm_FF2: "cmod (FF2 r p N t) \<le> Ec r p N"
  unfolding FF2_def Ec_def
proof (rule order_trans [OF norm_sum], rule sum_mono)
  fix j
  have "cmod ((- psi1 p j t) *\<^sub>R (\<i> * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) + psi p j t *\<^sub>R (\<i> * cis (- psi p j t)))
        \<le> (psi1 p j t)\<^sup>2 + \<bar>psi p j t\<bar>"
    by (rule order_trans [OF norm_triangle_ineq]) (simp add: norm_mult power2_eq_square abs_mult)
  also have "\<dots> \<le> (gam p j)\<^sup>2 + gam p j"
  proof -
    have "(psi1 p j t)\<^sup>2 \<le> (gam p j)\<^sup>2"
      by (metis psi1_bound power_mono abs_ge_zero power2_abs)
    then show ?thesis using psi_bound [of p j t] by linarith
  qed
  finally show "cmod (r j * ((- psi1 p j t) *\<^sub>R (\<i> * ((- psi1 p j t) *\<^sub>R (\<i> * cis (- psi p j t)))) + psi p j t *\<^sub>R (\<i> * cis (- psi p j t))))
                \<le> cmod (r j) * (gam p j + (gam p j)\<^sup>2)"
    by (simp add: norm_mult mult_left_mono add.commute)
qed

section \<open>The squared pattern and its derivatives\<close>

definition SS :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "SS r p N t = (cmod (FF r p N t))\<^sup>2"
definition SS1 :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "SS1 r p N t = 2 * inner (FF r p N t) (FF1 r p N t)"
definition SS2 :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "SS2 r p N t = 2 * (inner (FF1 r p N t) (FF1 r p N t) + inner (FF r p N t) (FF2 r p N t))"

lemma SS_inner: "SS r p N t = inner (FF r p N t) (FF r p N t)"
  by (simp add: SS_def power2_norm_eq_inner)

lemma DERIV_inner_vec:
  assumes "(f has_vector_derivative f') (at t)" "(g has_vector_derivative g') (at t)"
  shows "DERIV (\<lambda>t. inner (f t) (g t)) t :> inner (f t) g' + inner f' (g t)"
proof -
  have fact: "((\<lambda>t. inner (f t) (g t)) has_derivative (\<lambda>h. inner (f t) (h *\<^sub>R g') + inner (h *\<^sub>R f') (g t))) (at t)"
    using assms unfolding has_vector_derivative_def by (rule has_derivative_inner)
  have eq: "(\<lambda>h. inner (f t) (h *\<^sub>R g') + inner (h *\<^sub>R f') (g t)) = (*) (inner (f t) g' + inner f' (g t))"
    by (simp add: fun_eq_iff inner_scaleR_left inner_scaleR_right algebra_simps)
  show ?thesis unfolding has_field_derivative_def using fact unfolding eq .
qed

lemma DERIV_SS: "DERIV (SS r p N) t :> SS1 r p N t"
proof -
  have "DERIV (\<lambda>t. inner (FF r p N t) (FF r p N t)) t :> inner (FF r p N t) (FF1 r p N t) + inner (FF1 r p N t) (FF r p N t)"
    by (rule DERIV_inner_vec [OF FF_deriv FF_deriv])
  then show ?thesis unfolding SS_inner [abs_def] SS1_def by (simp add: inner_commute)
qed

lemma DERIV_SS1: "DERIV (SS1 r p N) t :> SS2 r p N t"
proof -
  have "DERIV (\<lambda>t. inner (FF r p N t) (FF1 r p N t)) t :> inner (FF r p N t) (FF2 r p N t) + inner (FF1 r p N t) (FF1 r p N t)"
    by (rule DERIV_inner_vec [OF FF_deriv FF1_deriv])
  then show ?thesis unfolding SS1_def SS2_def by (intro DERIV_cmult) (simp add: add.commute)
qed

lemma SS2_bound: "\<bar>SS2 r p N t\<bar> \<le> Hc r p N"
proof -
  have "\<bar>inner (FF1 r p N t) (FF1 r p N t)\<bar> \<le> (Dc r p N)\<^sup>2"
    using norm_FF1 [of r p N t] by (simp add: power2_norm_eq_inner [symmetric] power_mono)
  moreover have "\<bar>inner (FF r p N t) (FF2 r p N t)\<bar> \<le> Bc r N * Ec r p N"
    using Cauchy_Schwarz_ineq2 [of "FF r p N t" "FF2 r p N t"] norm_FF [of r p N t] norm_FF2 [of r p N t]
    by (meson mult_mono norm_ge_zero order_trans)
  moreover have "\<bar>inner (FF1 r p N t) (FF1 r p N t) + inner (FF r p N t) (FF2 r p N t)\<bar>
                 \<le> \<bar>inner (FF1 r p N t) (FF1 r p N t)\<bar> + \<bar>inner (FF r p N t) (FF2 r p N t)\<bar>"
    by (rule abs_triangle_ineq)
  ultimately have "\<bar>inner (FF1 r p N t) (FF1 r p N t) + inner (FF r p N t) (FF2 r p N t)\<bar> \<le> (Dc r p N)\<^sup>2 + Bc r N * Ec r p N"
    by linarith
  then show ?thesis unfolding SS2_def Hc_def by (simp add: abs_mult)
qed

text \<open>Lemma 2.4, first bound.\<close>
theorem SS_taylor:
  "\<bar>SS r p N t - SS r p N c\<bar> \<le> \<bar>SS1 r p N c\<bar> * \<bar>t - c\<bar> + Hc r p N / 2 * (t - c)\<^sup>2"
  by (rule taylor2_bound [OF DERIV_SS DERIV_SS1 SS2_bound])

text \<open>Lemma 2.4, second bound: the difference of two squared patterns.\<close>
theorem SS_diff_taylor:
  "\<bar>(SS r p N t - SS r' p N t) - (SS r p N c - SS r' p N c)\<bar>
     \<le> \<bar>SS1 r p N c - SS1 r' p N c\<bar> * \<bar>t - c\<bar> + (Hc r p N + Hc r' p N) / 2 * (t - c)\<^sup>2"
proof -
  have d1: "\<And>t. DERIV (\<lambda>t. SS r p N t - SS r' p N t) t :> SS1 r p N t - SS1 r' p N t"
    by (intro DERIV_diff DERIV_SS)
  have d2: "\<And>t. DERIV (\<lambda>t. SS1 r p N t - SS1 r' p N t) t :> SS2 r p N t - SS2 r' p N t"
    by (intro DERIV_diff DERIV_SS1)
  have K: "\<And>t. \<bar>SS2 r p N t - SS2 r' p N t\<bar> \<le> Hc r p N + Hc r' p N"
    using SS2_bound [of r p N] SS2_bound [of r' p N] by (meson abs_triangle_ineq4 add_mono order_trans)
  show ?thesis by (rule taylor2_bound [OF d1 d2 K])
qed

text \<open>Connection to the grid pattern after corrections \<open>\<sigma>\<close> (Lemma 2.2): \<open>sq\<close> at index \<open>m\<close> is \<open>SS\<close> of the rows.\<close>
lemma sq_exc_SS: "sq p N (exc p N (c0 p t) \<sigma>) m = SS (rows p N \<sigma> m) p N t"
  by (simp add: sq_def SS_def FF_c0 patt_exc_rows)

end
