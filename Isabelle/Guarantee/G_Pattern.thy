theory G_Pattern
  imports "Perturbative_Termination.Algorithm" G_Chord
begin

section \<open>The pattern as a function of the look direction\<close>

text \<open>\<open>pw\<close> is the true squared pattern at every real direction; \<open>sq\<close> is its value at a grid point.\<close>

definition pw :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> real" where
  "pw p N c \<phi> = (cmod (patt p N c \<phi>))\<^sup>2"

lemma sq_pw: "sq p N c m = pw p N c (grid m)"
  by (simp add: sq_def pw_def)

lemma cnj_patt: "cnj (patt p N c \<phi>) = FF (\<lambda>j. cnj (c j)) p N \<phi>"
  by (simp add: patt_def FF_def steer_def psi_def cis_cnj mult.commute)

lemma pw_SS: "pw p N c \<phi> = SS (\<lambda>j. cnj (c j)) p N \<phi>"
  by (simp add: pw_def SS_def flip: cnj_patt)

lemma Hc_cnj: "Hc (\<lambda>j. cnj (c j)) p N = Hc c p N"
  by (simp add: Hc_def Bc_def Dc_def Ec_def)

lemma Hc_ge0: "0 \<le> Hc c p N"
proof -
  have "0 \<le> Bc c N" by (simp add: Bc_def sum_nonneg)
  moreover have "0 \<le> gam p j" for j by (simp add: gam_def kw_def)
  then have "0 \<le> Ec c p N" by (simp add: Ec_def sum_nonneg)
  ultimately show ?thesis by (simp add: Hc_def)
qed

text \<open>Fact 2 for the pattern: between two directions \<open>h\<close> apart, it exceeds the larger end value,
  or falls below the smaller, by at most \<open>Hc h\<^sup>2 / 8\<close>.\<close>

theorem pw_cell_max:
  assumes "a \<le> x" "x \<le> b"
  shows "pw p N c x \<le> max (pw p N c a) (pw p N c b) + Hc c p N * (b - a)\<^sup>2 / 8"
  using chord_max [OF DERIV_SS DERIV_SS1 SS2_bound assms, of "\<lambda>j. cnj (c j)" p N]
  by (simp add: pw_SS Hc_cnj)

theorem pw_cell_min:
  assumes "a \<le> x" "x \<le> b"
  shows "pw p N c x \<ge> min (pw p N c a) (pw p N c b) - Hc c p N * (b - a)\<^sup>2 / 8"
  using chord_min [OF DERIV_SS DERIV_SS1 SS2_bound assms, of "\<lambda>j. cnj (c j)" p N]
  by (simp add: pw_SS Hc_cnj)

section \<open>Periodicity and lifts of grid points\<close>

lemma steer_period: "steer p (\<phi> + 2 * pi * of_int z) j = steer p \<phi> j"
  by (simp add: steer_def cos_add sin_add)

lemma pw_period: "pw p N c (\<phi> + 2 * pi * of_int z) = pw p N c \<phi>"
  by (simp add: pw_def patt_def steer_period)

text \<open>\<open>x\<close> is a lift of grid index \<open>j\<close> if it is \<open>\<phi>\<^sub>j\<close> plus a multiple of \<open>2\<pi>\<close>.\<close>
definition lift :: "nat \<Rightarrow> real \<Rightarrow> bool" where
  "lift j x \<longleftrightarrow> (\<exists>z::int. x = grid j + 2 * pi * of_int z)"

definition hM :: real where "hM = 2 * pi / real M"

lemma hM_pos: "0 < hM"
  by (simp add: hM_def M_def)

lemma grid_Suc: "grid (Suc m) = grid m + hM"
  by (simp add: grid_def hM_def M_def field_simps)

lemma grid_M: "grid M = 2 * pi"
  by (simp add: grid_def M_def)

lemma pw_lift: "lift j x \<Longrightarrow> pw p N c x = sq p N c j"
  unfolding lift_def sq_pw by (auto simp: pw_period)

lemma lift_grid: "lift j (grid j)"
  unfolding lift_def by (rule exI [of _ 0]) simp

lemma lift_shift: "lift j x \<Longrightarrow> lift j (x + 2 * pi * of_int z)"
  unfolding lift_def by (auto intro: exI [of _ "_ + z"] simp: algebra_simps)

lemma lift_next:
  assumes m: "m < M" and l: "lift m x"
  shows "lift (next_idx m) (x + hM)"
proof (cases "Suc m < M")
  case True
  then have "next_idx m = Suc m" by (simp add: next_idx_def)
  with l show ?thesis by (auto simp: lift_def grid_Suc algebra_simps)
next
  case False
  with m have sm: "Suc m = M" by simp
  then have n: "next_idx m = 0" by (simp add: next_idx_def)
  from l obtain z :: int where z: "x = grid m + 2 * pi * of_int z" by (auto simp: lift_def)
  have "x + hM = grid (Suc m) + 2 * pi * of_int z" using z by (simp add: grid_Suc)
  also have "\<dots> = grid 0 + 2 * pi * of_int (z + 1)" using sm grid_M by (simp add: grid_def algebra_simps)
  finally have "x + hM = grid 0 + 2 * pi * of_int (z + 1)" .
  then show ?thesis unfolding lift_def n by blast
qed

lemma lift_prev:
  assumes m: "m < M" and l: "lift m x"
  shows "lift (prev_idx m) (x - hM)"
proof (cases m)
  case 0
  then have p: "prev_idx m = M - 1" by (simp add: prev_idx_def M_def)
  from l obtain z :: int where z: "x = grid m + 2 * pi * of_int z" by (auto simp: lift_def)
  have g: "grid (M - 1) + hM = 2 * pi" using grid_Suc [of "M - 1"] grid_M by (simp add: M_def)
  have "x - hM = grid (M - 1) + 2 * pi * of_int (z - 1)" using z 0 g by (simp add: grid_def algebra_simps)
  then show ?thesis unfolding lift_def p by blast
next
  case (Suc k)
  with m have p: "prev_idx m = k" by (simp add: prev_idx_def)
  from l obtain z :: int where z: "x = grid m + 2 * pi * of_int z" by (auto simp: lift_def)
  have "x - hM = grid k + 2 * pi * of_int z" using z Suc by (simp add: grid_Suc)
  then show ?thesis unfolding lift_def p by blast
qed

lemma next_prev:
  assumes m: "m < M" shows "next_idx (prev_idx m) = m"
proof (cases m)
  case 0 then show ?thesis by (simp add: prev_idx_def next_idx_def M_def)
next
  case (Suc k)
  with m have "prev_idx m = k" by (simp add: prev_idx_def)
  with Suc m show ?thesis by (simp add: next_idx_def)
qed

lemma idx_prev_lt: "prev_idx m < M" and idx_next_lt: "next_idx m < M"
  by (simp_all add: prev_idx_def next_idx_def M_def)

section \<open>The weights stay in the ball of radius \<open>\<surd>N\<close>\<close>

definition nrm :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real" where
  "nrm N c = (\<Sum>j<N. (cmod (c j))\<^sup>2)"

lemma cmod_add_sq: "(cmod (x + y))\<^sup>2 = (cmod x)\<^sup>2 + (cmod y)\<^sup>2 + 2 * Re (x * cnj y)"
  unfolding cmod_power2 by (simp add: power2_eq_square algebra_simps)

text \<open>A correction is an orthogonal projection, so it does not increase the norm.\<close>
lemma nrm_corr: "nrm N (corr p N s c) \<le> nrm N c"
proof -
  define F where "F = patt p N c (grid s)"
  define u where "u = corr p N s c"
  define v where "v j = F / of_nat N * cnj (steer p (grid s) j)" for j
  have cuv: "c j = u j + v j" for j by (simp add: u_def v_def F_def corr_def)
  have orth: "(\<Sum>j<N. u j * cnj (v j)) = 0"
  proof -
    have "(\<Sum>j<N. u j * cnj (v j)) = (\<Sum>j<N. cnj (F / of_nat N) * (steer p (grid s) j * u j))"
      by (intro sum.cong) (simp_all add: v_def algebra_simps)
    also have "\<dots> = cnj (F / of_nat N) * patt p N u (grid s)"
      by (simp add: patt_def sum_distrib_left)
    also have "patt p N u (grid s) = 0" unfolding u_def by (rule patt_corr_self)
    finally show ?thesis by simp
  qed
  have "nrm N c = (\<Sum>j<N. (cmod (u j))\<^sup>2 + (cmod (v j))\<^sup>2 + 2 * Re (u j * cnj (v j)))"
    by (simp add: nrm_def cuv cmod_add_sq)
  also have "\<dots> = nrm N u + (\<Sum>j<N. (cmod (v j))\<^sup>2) + 2 * Re (\<Sum>j<N. u j * cnj (v j))"
    by (simp add: nrm_def sum.distrib sum_distrib_left Re_sum)
  also have "\<dots> = nrm N u + (\<Sum>j<N. (cmod (v j))\<^sup>2)" by (simp add: orth)
  finally show ?thesis unfolding u_def by (simp add: sum_nonneg)
qed

lemma nrm_c0: "nrm N (c0 p t) = real N"
  by (simp add: nrm_def c0_def)

lemma Bc_sq: "(Bc c N)\<^sup>2 \<le> real N * nrm N c"
proof -
  have "(\<Sum>j<N. cmod (c j) * 1)\<^sup>2 \<le> (\<Sum>j<N. (cmod (c j))\<^sup>2) * (\<Sum>j<N. 1\<^sup>2)"
    by (rule Cauchy_Schwarz_ineq_sum)
  then show ?thesis by (simp add: Bc_def nrm_def mult.commute)
qed

text \<open>The curvature constant in terms of the norm, for a bound \<open>G\<close> on \<open>k |p\<^sub>j|\<close>.\<close>
lemma Hc_le:
  assumes G: "\<And>j. j < N \<Longrightarrow> gam p j \<le> G"
  shows "Hc c p N \<le> 2 * (Bc c N)\<^sup>2 * (G + 2 * G\<^sup>2)"
proof -
  have g0: "0 \<le> gam p j" for j by (simp add: gam_def kw_def)
  have B0: "0 \<le> Bc c N" by (simp add: Bc_def sum_nonneg)
  have "Dc c p N \<le> Bc c N * G"
    unfolding Dc_def Bc_def sum_distrib_right by (intro sum_mono mult_left_mono G) auto
  moreover have "0 \<le> Dc c p N" by (simp add: Dc_def sum_nonneg g0)
  ultimately have D: "(Dc c p N)\<^sup>2 \<le> (Bc c N * G)\<^sup>2" by (intro power_mono) auto
  have "gam p j + (gam p j)\<^sup>2 \<le> G + G\<^sup>2" if "j < N" for j
    using G [OF that] g0 [of j] by (intro add_mono power_mono) auto
  then have "Ec c p N \<le> Bc c N * (G + G\<^sup>2)"
    unfolding Ec_def Bc_def sum_distrib_right by (intro sum_mono mult_left_mono) auto
  then have E: "Bc c N * Ec c p N \<le> Bc c N * (Bc c N * (G + G\<^sup>2))"
    using B0 by (intro mult_left_mono) auto
  have "Hc c p N = 2 * ((Dc c p N)\<^sup>2 + Bc c N * Ec c p N)" by (simp add: Hc_def)
  also have "\<dots> \<le> 2 * ((Bc c N * G)\<^sup>2 + Bc c N * (Bc c N * (G + G\<^sup>2)))"
    using D E by simp
  also have "\<dots> = 2 * (Bc c N)\<^sup>2 * (G + 2 * G\<^sup>2)"
    by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed

theorem Hc_le_norm:
  assumes G: "\<And>j. j < N \<Longrightarrow> gam p j \<le> G" and n: "nrm N c \<le> real N"
  shows "Hc c p N \<le> 2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2)"
proof -
  have G0: "0 \<le> G + 2 * G\<^sup>2" if "N > 0"
  proof -
    have "0 \<le> gam p 0" by (simp add: gam_def kw_def)
    then have "0 \<le> G" using G that by (meson order_trans)
    then show ?thesis by simp
  qed
  show ?thesis
  proof (cases "N = 0")
    case True then show ?thesis by (simp add: Hc_def Bc_def Dc_def Ec_def)
  next
    case False
    have "(Bc c N)\<^sup>2 \<le> real N * real N"
      using Bc_sq [of c N] n by (meson mult_left_mono of_nat_0_le_iff order_trans)
    then have "2 * (Bc c N)\<^sup>2 * (G + 2 * G\<^sup>2) \<le> 2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2)"
      using G0 False by (intro mult_right_mono) (auto simp: power2_eq_square)
    moreover have "Hc c p N \<le> 2 * (Bc c N)\<^sup>2 * (G + 2 * G\<^sup>2)" by (rule Hc_le) (rule G)
    ultimately show ?thesis by linarith
  qed
qed

end
