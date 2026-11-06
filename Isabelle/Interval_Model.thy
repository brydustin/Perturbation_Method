theory Interval_Model
  imports Algorithm "HOL-Library.Interval_Float" "HOL-Decision_Procs.Approximation_Bounds"
begin

section \<open>Complex intervals\<close>

text \<open>A complex interval is a pair of float intervals (real and imaginary parts).  All
  operations take a precision \<open>p\<close> and round outward, using the verified operations of
  \<open>Approximation_Bounds\<close>.\<close>

type_synonym civ = "float interval \<times> float interval"

definition cin :: "complex \<Rightarrow> civ \<Rightarrow> bool" where
  "cin z Z \<longleftrightarrow> Re z \<in>\<^sub>r fst Z \<and> Im z \<in>\<^sub>r snd Z"

text \<open>The complex operations are exact (floats are exact dyadic rationals); rounding to precision \<open>p\<close>
  happens only when a row is stored (\<open>cround\<close>).  The precision argument is kept for uniformity.\<close>
definition cadd :: "nat \<Rightarrow> civ \<Rightarrow> civ \<Rightarrow> civ" where
  "cadd p Z W = (fst Z + fst W, snd Z + snd W)"

definition cneg :: "civ \<Rightarrow> civ" where "cneg Z = (- fst Z, - snd Z)"

definition csub :: "nat \<Rightarrow> civ \<Rightarrow> civ \<Rightarrow> civ" where "csub p Z W = cadd p Z (cneg W)"

definition cmul :: "nat \<Rightarrow> civ \<Rightarrow> civ \<Rightarrow> civ" where
  "cmul p Z W = (fst Z * fst W + (- (snd Z * snd W)), fst Z * snd W + snd Z * fst W)"

definition ccnj :: "civ \<Rightarrow> civ" where "ccnj Z = (fst Z, - snd Z)"

text \<open>Scaling by a real interval.\<close>
definition cscale :: "nat \<Rightarrow> float interval \<Rightarrow> civ \<Rightarrow> civ" where
  "cscale p A Z = (A * fst Z, A * snd Z)"

definition cnorm2 :: "nat \<Rightarrow> civ \<Rightarrow> float interval" where
  "cnorm2 p Z = fst Z * fst Z + snd Z * snd Z"

definition cround :: "nat \<Rightarrow> civ \<Rightarrow> civ" where
  "cround p Z = (round_interval p (fst Z), round_interval p (snd Z))"

definition czero :: civ where "czero = (0, 0)"

primrec csum :: "nat \<Rightarrow> civ list \<Rightarrow> civ" where
  "csum p [] = czero"
| "csum p (Z # Zs) = cadd p Z (csum p Zs)"

lemma cin_add: "cin z Z \<Longrightarrow> cin w W \<Longrightarrow> cin (z + w) (cadd p Z W)"
  by (auto simp: cin_def cadd_def intro!: plus_in_float_intervalI)

lemma cin_round: "cin z Z \<Longrightarrow> cin z (cround p Z)"
  by (auto simp: cin_def cround_def intro!: in_round_intervalI)

lemma cin_neg: "cin z Z \<Longrightarrow> cin (- z) (cneg Z)"
  by (auto simp: cin_def cneg_def intro!: uminus_in_float_intervalI)

lemma cin_sub: "cin z Z \<Longrightarrow> cin w W \<Longrightarrow> cin (z - w) (csub p Z W)"
  unfolding csub_def using cin_add [OF _ cin_neg [of w W], of z Z p] by simp

lemma cin_mul:
  assumes "cin z Z" "cin w W"
  shows "cin (z * w) (cmul p Z W)"
proof -
  from assms have a: "Re z \<in>\<^sub>r fst Z" "Im z \<in>\<^sub>r snd Z" "Re w \<in>\<^sub>r fst W" "Im w \<in>\<^sub>r snd W"
    by (simp_all add: cin_def)
  have "Re z * Re w + (- (Im z * Im w)) \<in>\<^sub>r fst Z * fst W + (- (snd Z * snd W))"
    by (intro plus_in_float_intervalI times_in_float_intervalI uminus_in_float_intervalI a)
  moreover have "Re z * Im w + Im z * Re w \<in>\<^sub>r fst Z * snd W + snd Z * fst W"
    by (intro plus_in_float_intervalI times_in_float_intervalI a)
  ultimately show ?thesis by (simp add: cin_def cmul_def)
qed

lemma cin_cnj: "cin z Z \<Longrightarrow> cin (cnj z) (ccnj Z)"
  by (auto simp: cin_def ccnj_def intro!: uminus_in_float_intervalI)

lemma cin_scale: "a \<in>\<^sub>r A \<Longrightarrow> cin z Z \<Longrightarrow> cin (a *\<^sub>R z) (cscale p A Z)"
  by (auto simp: cin_def cscale_def intro!: times_in_float_intervalI)

lemma cin_zero: "cin 0 czero"
  by (simp add: cin_def czero_def zero_in_float_intervalI)

lemma cin_norm2: "cin z Z \<Longrightarrow> (cmod z)\<^sup>2 \<in>\<^sub>r cnorm2 p Z"
  unfolding cmod_power2
  unfolding cnorm2_def cin_def power2_eq_square
  by (intro plus_in_float_intervalI times_in_float_intervalI) simp_all

lemma cin_sum:
  assumes "length zs = length Zs" "\<And>i. i < length zs \<Longrightarrow> cin (zs ! i) (Zs ! i)"
  shows "cin (sum_list zs) (csum p Zs)"
  using assms
proof (induction zs arbitrary: Zs)
  case Nil then show ?case by (simp add: cin_zero)
next
  case (Cons z zs)
  then obtain Z Zs' where Zs: "Zs = Z # Zs'" by (cases Zs) auto
  have "cin z Z" using Cons.prems(2) [of 0] by (simp add: Zs)
  moreover have "cin (sum_list zs) (csum p Zs')"
  proof (intro Cons.IH)
    show "length zs = length Zs'" using Cons.prems(1) by (simp add: Zs)
    fix i assume "i < length zs"
    then show "cin (zs ! i) (Zs' ! i)" using Cons.prems(2) [of "Suc i"] by (simp add: Zs)
  qed
  ultimately show ?case by (simp add: Zs cin_add)
qed

text \<open>Sums over \<open>{..<N}\<close> as list sums.\<close>
lemma sum_lessThan_sum_list: "(\<Sum>j<N. f j) = sum_list (map f [0..<N])"
  by (simp add: sum_list_distinct_conv_sum_set atLeast_upt)

section \<open>Enclosures of the elementary functions\<close>

definition pi_ivl :: "nat \<Rightarrow> float interval" where "pi_ivl p = pi_float_interval p"

lemma pi_in: "pi \<in>\<^sub>r pi_ivl p"
  by (simp add: pi_ivl_def pi_float_interval)

definition half_pi_ivl :: "nat \<Rightarrow> float interval" where
  "half_pi_ivl p = mult_float_interval p (interval_of (Float 1 (-1))) (pi_ivl p)"

lemma half_pi_in: "pi / 2 \<in>\<^sub>r half_pi_ivl p"
proof -
  have "real_of_float (Float 1 (-1)) * pi \<in>\<^sub>r half_pi_ivl p"
    unfolding half_pi_ivl_def by (intro mult_float_intervalI interval_of pi_in)
  then show ?thesis by (simp add: real_of_float_eq [symmetric] Float.compute_float_numeral) 
qed

definition sin_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> float interval" where
  "sin_ivl p X = cos_float_interval p (plus_float_interval p X (- half_pi_ivl p))"

lemma sin_in: "x \<in>\<^sub>r X \<Longrightarrow> sin x \<in>\<^sub>r sin_ivl p X"
proof -
  assume "x \<in>\<^sub>r X"
  then have "x + (- (pi / 2)) \<in>\<^sub>r plus_float_interval p X (- half_pi_ivl p)"
    by (intro plus_float_intervalI uminus_in_float_intervalI half_pi_in)
  then have "cos (x - pi / 2) \<in>\<^sub>r sin_ivl p X"
    unfolding sin_ivl_def by (intro cos_float_intervalI) simp
  moreover have "cos (x - pi / 2) = sin x" by (simp add: cos_diff)
  ultimately show ?thesis by simp
qed

definition cis_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> civ" where
  "cis_ivl p X = (cos_float_interval p X, sin_ivl p X)"

lemma cin_cis: "x \<in>\<^sub>r X \<Longrightarrow> cin (cis x) (cis_ivl p X)"
  by (simp add: cin_def cis_ivl_def cos_float_intervalI sin_in)

section \<open>The array with float positions\<close>

text \<open>Positions are given as floats (the double-precision numbers of the input file).\<close>
definition fpos :: "(nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> real \<times> real" where
  "fpos q j = (real_of_float (fst (q j)), real_of_float (snd (q j)))"

definition kw_ivl :: "nat \<Rightarrow> float interval" where
  "kw_ivl p = mult_float_interval p (interval_of (Float 20 0)) (pi_ivl p)"

lemma kw_in: "kw \<in>\<^sub>r kw_ivl p"
  unfolding kw_ivl_def kw_def
  using mult_float_intervalI [OF interval_of pi_in, of "Float 20 0" p] by (simp add: Float.compute_float_numeral)

text \<open>\<open>1/M\<close> as an explicit dyadic enclosure (\<open>2\<^sup>6\<^sup>0/1000 = 1152921504606846.976\<close>).\<close>
definition inv_M_ivl :: "float interval" where
  "inv_M_ivl = Ivl (Float 1152921504606846 (-60)) (Float 1152921504606847 (-60))"

lemma inv_M_in: "1 / real M \<in>\<^sub>r inv_M_ivl"
  unfolding inv_M_ivl_def M_def
  by (intro in_real_intervalI) (simp_all add: Ivl_simps real_of_float_eq)

definition grid_ivl :: "nat \<Rightarrow> nat \<Rightarrow> float interval" where
  "grid_ivl p m = mult_float_interval p (mult_float_interval p (interval_of (Float 2 0)) (pi_ivl p))
                    (mult_float_interval p (interval_of (Float (int m) 0)) inv_M_ivl)"

lemma grid_in: "grid m \<in>\<^sub>r grid_ivl p m"
proof -
  have "(real_of_float (Float 2 0) * pi) * (real_of_float (Float (int m) 0) * (1 / real M)) \<in>\<^sub>r grid_ivl p m"
    unfolding grid_ivl_def by (intro mult_float_intervalI interval_of pi_in inv_M_in)
  moreover have "(real_of_float (Float 2 0) * pi) * (real_of_float (Float (int m) 0) * (1 / real M)) = grid m"
    by (simp add: grid_def Float.compute_float_numeral)
  ultimately show ?thesis by simp
qed

definition phase_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> float interval \<Rightarrow> nat \<Rightarrow> float interval" where
  "phase_ivl p q X j = mult_float_interval p (kw_ivl p)
     (plus_float_interval p (mult_float_interval p (interval_of (fst (q j))) (cos_float_interval p X))
                            (mult_float_interval p (interval_of (snd (q j))) (sin_ivl p X)))"

lemma phase_in: "x \<in>\<^sub>r X \<Longrightarrow> psi (fpos q) j x \<in>\<^sub>r phase_ivl p q X j"
  unfolding phase_ivl_def psi_def fpos_def
  by (intro mult_float_intervalI plus_float_intervalI kw_in interval_of cos_float_intervalI sin_in) simp_all

definition steer_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> float interval \<Rightarrow> nat \<Rightarrow> civ" where
  "steer_ivl p q X j = cis_ivl p (phase_ivl p q X j)"

lemma steer_psi: "steer (fpos q) x j = cis (psi (fpos q) j x)"
  by (simp add: steer_def psi_def)

lemma cin_steer: "x \<in>\<^sub>r X \<Longrightarrow> cin (steer (fpos q) x j) (steer_ivl p q X j)"
  unfolding steer_ivl_def steer_psi by (intro cin_cis phase_in)

text \<open>The initial excitation \<open>c0 = cnj (steer t)\<close>.\<close>
definition c0_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> float interval \<Rightarrow> nat \<Rightarrow> civ" where
  "c0_ivl p q X j = ccnj (steer_ivl p q X j)"

lemma cin_c0: "x \<in>\<^sub>r X \<Longrightarrow> cin (c0 (fpos q) x j) (c0_ivl p q X j)"
  unfolding c0_def c0_ivl_def by (intro cin_cnj cin_steer)

section \<open>Interval rows\<close>

definition kernel_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> civ" where
  "kernel_ivl p q m j = steer_ivl p q (grid_ivl p m) j"

lemma cin_kernel: "cin (steer (fpos q) (grid m) j) (kernel_ivl p q m j)"
  unfolding kernel_ivl_def by (intro cin_steer grid_in)

text \<open>\<open>1/N\<close> is supplied as an enclosure \<open>IN\<close>.\<close>
definition gram_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> civ" where
  "gram_ivl p q N IN m s = cscale p IN (csum p (map (\<lambda>j. cmul p (kernel_ivl p q m j) (ccnj (kernel_ivl p q s j))) [0..<N]))"

lemma cin_gram:
  assumes "1 / real N \<in>\<^sub>r IN"
  shows "cin (gram (fpos q) N m s) (gram_ivl p q N IN m s)"
proof -
  have "gram (fpos q) N m s = (1 / real N) *\<^sub>R (\<Sum>j<N. steer (fpos q) (grid m) j * cnj (steer (fpos q) (grid s) j))"
    unfolding gram_def scaleR_conv_of_real of_real_divide of_real_1 of_real_of_nat_eq
    by (simp add: divide_inverse mult.commute)
  also have "cin \<dots> (gram_ivl p q N IN m s)"
    unfolding gram_ivl_def sum_lessThan_sum_list
    by (intro cin_scale [OF assms] cin_sum) (simp_all add: cin_mul cin_cnj cin_kernel)
  finally show ?thesis .
qed

primrec rows_ivl :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> civ" where
  "rows_ivl p q N IN [] m j = kernel_ivl p q m j"
| "rows_ivl p q N IN (s # \<sigma>) m j = cround p (csub p (rows_ivl p q N IN \<sigma> m j) (cmul p (cround p (gram_ivl p q N IN m s)) (rows_ivl p q N IN \<sigma> s j)))"

lemma cin_rows:
  assumes "1 / real N \<in>\<^sub>r IN"
  shows "cin (rows (fpos q) N \<sigma> m j) (rows_ivl p q N IN \<sigma> m j)"
  by (induction \<sigma> arbitrary: m) (simp_all add: cin_kernel cin_round cin_sub cin_mul cin_gram [OF assms])

end
