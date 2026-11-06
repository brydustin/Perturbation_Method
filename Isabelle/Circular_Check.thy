theory Circular_Check
  imports Circular_Floor Circular_Data
begin

section \<open>Enclosures of the circular array's steering vectors\<close>

lemma upper_in: "x \<in>\<^sub>r X \<Longrightarrow> x \<le> real_of_float (upper X)" by (simp add: set_of_eq)

definition rc_ivl :: "float interval" where
  "rc_ivl = Ivl (Float 3602879701896396 (-53)) (Float 3602879701896397 (-53))"

lemma rc_in: "rc \<in>\<^sub>r rc_ivl"
  unfolding rc_ivl_def rc_def by (intro in_real_intervalI) (simp_all add: Ivl_simps real_of_float_eq)

definition theta_ivl :: "nat \<Rightarrow> nat \<Rightarrow> float interval" where
  "theta_ivl p j = mult_float_interval p (pi_ivl p) (interval_of (Float (int j) (-4)))"

lemma theta_in: "theta j \<in>\<^sub>r theta_ivl p j"
proof -
  have "real_of_float (Float (int j) (-4)) = real j / 16" by (simp add: powr_minus_divide)
  then have "theta j = pi * real_of_float (Float (int j) (-4))" unfolding theta_def by simp
  then show ?thesis unfolding theta_ivl_def by (simp only:) (intro mult_float_intervalI pi_in interval_of)
qed

definition ux_ivl :: "nat \<Rightarrow> nat \<Rightarrow> float interval" where
  "ux_ivl p j = mult_float_interval p rc_ivl (cos_float_interval p (theta_ivl p j))"
definition uy_ivl :: "nat \<Rightarrow> nat \<Rightarrow> float interval" where
  "uy_ivl p j = mult_float_interval p rc_ivl (sin_ivl p (theta_ivl p j))"

definition ust_ivl :: "nat \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> civ" where
  "ust_ivl p X Y CG SG = cis_ivl p (mult_float_interval p (kw_ivl p)
      (plus_float_interval p (mult_float_interval p X CG) (mult_float_interval p Y SG)))"

lemma cin_ust:
  assumes "fst (ucp j) \<in>\<^sub>r X" "snd (ucp j) \<in>\<^sub>r Y" "cos \<phi> \<in>\<^sub>r CG" "sin \<phi> \<in>\<^sub>r SG"
  shows "cin (steer ucp \<phi> j) (ust_ivl p X Y CG SG)"
  unfolding ust_ivl_def steer_def
  by (intro cin_cis mult_float_intervalI plus_float_intervalI kw_in assms)

lemma ux_in: "fst (ucp j) \<in>\<^sub>r ux_ivl p j"
  unfolding ux_ivl_def ucp_def fst_conv by (intro mult_float_intervalI rc_in cos_float_intervalI theta_in)
lemma uy_in: "snd (ucp j) \<in>\<^sub>r uy_ivl p j"
  unfolding uy_ivl_def ucp_def snd_conv by (intro mult_float_intervalI rc_in sin_in theta_in)

text \<open>The table of all steering vectors on the grid.\<close>
definition ustL :: "nat \<Rightarrow> civ list list" where
  "ustL p = (let XY = map (\<lambda>j. (ux_ivl p j, uy_ivl p j)) [0..<32] in
     map (\<lambda>m. let G = grid_ivl p m; CG = cos_float_interval p G; SG = sin_ivl p G in
       map (\<lambda>XYj. ust_ivl p (fst XYj) (snd XYj) CG SG) XY) [0..<M])"

definition tbl_ok :: "civ list list \<Rightarrow> bool" where
  "tbl_ok T \<longleftrightarrow> length T = M \<and> (\<forall>m<M. length (T ! m) = 32 \<and> (\<forall>j<32. cin (steer ucp (grid m) j) (T ! m ! j)))"

lemma tbl_ok_ustL: "tbl_ok (ustL p)"
  unfolding tbl_ok_def ustL_def Let_def
  by (auto intro!: cin_ust ux_in uy_in cos_float_intervalI sin_in grid_in)

section \<open>Rounded sums\<close>

primrec rsum :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval" where
  "rsum p [] = 0"
| "rsum p (X # Xs) = round_interval p (X + rsum p Xs)"

lemma rsum_in: "list_all2 (\<lambda>x X. x \<in>\<^sub>r X) xs Xs \<Longrightarrow> sum_list xs \<in>\<^sub>r rsum p Xs"
proof (induction xs arbitrary: Xs)
  case Nil then show ?case by (simp add: zero_in_float_intervalI)
next
  case (Cons x xs)
  then obtain X Xs' where Xs: "Xs = X # Xs'" "x \<in>\<^sub>r X" "list_all2 (\<lambda>x X. x \<in>\<^sub>r X) xs Xs'"
    by (cases Xs) auto
  show ?case unfolding Xs(1) by (simp add: in_round_intervalI plus_in_float_intervalI Xs(2) Cons.IH [OF Xs(3)])
qed

lemma list_all2_map_map: "(\<And>x. x \<in> set xs \<Longrightarrow> P (f x) (g x)) \<Longrightarrow> list_all2 P (map f xs) (map g xs)"
  by (induction xs) auto

lemma rsum_map_in:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<in>\<^sub>r F x) \<Longrightarrow> sum_list (map f xs) \<in>\<^sub>r rsum p (map F xs)"
  by (rule rsum_in) (rule list_all2_map_map)

section \<open>The sidelobe region as a list\<close>

definition inQ :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "inQ \<Delta> m \<longleftrightarrow> m < M \<and> 100 * \<Delta> < 36 * min m (M - m)"

definition qlist :: "nat \<Rightarrow> nat list" where "qlist \<Delta> = filter (inQ \<Delta>) [0..<M]"

lemma set_qlist: "set (qlist \<Delta>) = Qset \<Delta>" unfolding qlist_def Qset_def inQ_def by auto
lemma distinct_qlist: "distinct (qlist \<Delta>)" unfolding qlist_def by simp

lemma sum_Qset: "(\<Sum>q\<in>Qset \<Delta>. f q) = sum_list (map f (qlist \<Delta>))"
  unfolding set_qlist [symmetric] by (rule sum.distinct_set_conv_list [OF distinct_qlist])

lemma sum_lt_list: "(\<Sum>i<n. f i) = sum_list (map f [0..<n])"
  by (simp add: sum_set_upt_conv_sum_list_nat [symmetric] atLeast0LessThan)

section \<open>The Gram matrix of the real form and the Cholesky residual\<close>

definition alphaI :: "civ list \<Rightarrow> nat \<Rightarrow> float interval" where
  "alphaI Z i = (if i < 32 then fst (Z ! i) else - snd (Z ! (i - 32)))"
definition betaI :: "civ list \<Rightarrow> nat \<Rightarrow> float interval" where
  "betaI Z i = (if i < 32 then snd (Z ! i) else fst (Z ! (i - 32)))"

lemma alpha_in:
  assumes "tbl_ok T" "q < M" "i < 64"
  shows "alpha q i \<in>\<^sub>r alphaI (T ! q) i"
  using assms unfolding tbl_ok_def alpha_def alphaI_def cin_def
  by (auto intro!: uminus_in_float_intervalI)

lemma beta_in:
  assumes "tbl_ok T" "q < M" "i < 64"
  shows "beta q i \<in>\<^sub>r betaI (T ! q) i"
  using assms unfolding tbl_ok_def beta_def betaI_def cin_def by auto

definition GI :: "nat \<Rightarrow> civ list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float interval" where
  "GI p R i k = rsum p (map (\<lambda>Z. round_interval p (alphaI Z i * alphaI Z k + betaI Z i * betaI Z k)) R)"

lemma GI_in:
  assumes T: "tbl_ok T" and ik: "i < 64" "k < 64"
  shows "Gm \<Delta> i k \<in>\<^sub>r GI p (map (\<lambda>q. T ! q) (qlist \<Delta>)) i k"
proof -
  have "Gm \<Delta> i k = sum_list (map (\<lambda>q. alpha q i * alpha q k + beta q i * beta q k) (qlist \<Delta>))"
    unfolding Gm_def sum_Qset ..
  also have "\<dots> \<in>\<^sub>r rsum p (map (\<lambda>q. round_interval p (alphaI (T ! q) i * alphaI (T ! q) k + betaI (T ! q) i * betaI (T ! q) k)) (qlist \<Delta>))"
  proof (rule rsum_map_in)
    fix q assume "q \<in> set (qlist \<Delta>)"
    then have q: "q < M" unfolding set_qlist Qset_def by simp
    show "alpha q i * alpha q k + beta q i * beta q k \<in>\<^sub>r round_interval p (alphaI (T ! q) i * alphaI (T ! q) k + betaI (T ! q) i * betaI (T ! q) k)"
      by (intro in_round_intervalI plus_in_float_intervalI times_in_float_intervalI alpha_in beta_in T q ik)
  qed
  finally show ?thesis unfolding GI_def by (simp add: comp_def)
qed

definition Lf :: "float list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where "Lf C i t = real_of_float (C ! i ! t)"

definition LLF :: "float list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float" where
  "LLF C i k = sum_list (map (\<lambda>t. C ! i ! t * C ! k ! t) [0..<64])"

lemma real_of_float_sum_list: "real_of_float (sum_list xs) = sum_list (map real_of_float xs)"
  by (induction xs) simp_all

lemma LLF_eq: "real_of_float (LLF C i k) = LLt (Lf C) i k"
  unfolding LLF_def LLt_def Lf_def sum_lt_list real_of_float_sum_list by (simp add: comp_def)

definition EI :: "nat \<Rightarrow> civ list list \<Rightarrow> float list list \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> float interval" where
  "EI p R C s2 i k = GI p R i k - interval_of (LLF C i k) - interval_of (if i = k then s2 else 0)"

lemma EI_in:
  assumes T: "tbl_ok T" and ik: "i < 64" "k < 64"
  shows "Gm \<Delta> i k - LLt (Lf C) i k - (if i = k then real_of_float s2 else 0) \<in>\<^sub>r EI p (map (\<lambda>q. T ! q) (qlist \<Delta>)) C s2 i k"
proof -
  have "(if i = k then real_of_float s2 else 0) = real_of_float (if i = k then s2 else 0)" by simp
  then show ?thesis unfolding EI_def LLF_eq [symmetric]
    by (simp only:) (intro minus_in_float_intervalI GI_in T ik interval_of)
qed

section \<open>Certificates\<close>

definition muF :: "(nat \<times> float \<times> float) list \<Rightarrow> nat \<Rightarrow> complex" where
  "muF l q = (case map_of l q of Some (a, b) \<Rightarrow> Complex (real_of_float a) (real_of_float b) | None \<Rightarrow> 0)"

definition cert_ok :: "nat \<Rightarrow> civ list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> float \<times> float) list \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "cert_ok p T \<Delta> \<psi> l Lam e \<longleftrightarrow> distinct (map fst l) \<and> list_all (\<lambda>x. inQ \<Delta> (fst x)) l \<and>
     upper (rsum p (map (\<lambda>x. sqrt_float_interval p (interval_of (fst (snd x) * fst (snd x) + snd (snd x) * snd (snd x)))) l)) \<le> Lam \<and>
     upper (rsum p (map (\<lambda>j. cnorm2 p (csub p (T ! \<psi> ! j)
        (csum p (map (\<lambda>x. cmul p (interval_of (fst (snd x)), interval_of (snd (snd x))) (T ! fst x ! j)) l)))) [0..<32])) \<le> e * e"

lemma sum_Qset_muF:
  assumes d: "distinct (map fst l)" and sub: "\<forall>x\<in>set l. inQ \<Delta> (fst x)" and g0: "\<And>q. g 0 q = (0::'b::comm_monoid_add)"
  shows "(\<Sum>q\<in>Qset \<Delta>. g (muF l q) q) = sum_list (map (\<lambda>x. g (Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x)))) (fst x)) l)"
proof -
  have S: "set (map fst l) \<subseteq> Qset \<Delta>" using sub unfolding Qset_def inQ_def by auto
  have "(\<Sum>q\<in>Qset \<Delta>. g (muF l q) q) = (\<Sum>q\<in>set (map fst l). g (muF l q) q)"
  proof (rule sum.mono_neutral_right [OF finite_Qset S], intro ballI)
    fix q assume "q \<in> Qset \<Delta> - set (map fst l)"
    then have "map_of l q = None" by (simp add: map_of_eq_None_iff)
    then show "g (muF l q) q = 0" by (simp add: muF_def g0)
  qed
  also have "\<dots> = sum_list (map (\<lambda>q. g (muF l q) q) (map fst l))" by (rule sum.distinct_set_conv_list [OF d])
  also have "\<dots> = sum_list (map (\<lambda>x. g (Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x)))) (fst x)) l)"
  proof -
    have "muF l (fst x) = Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x)))" if "x \<in> set l" for x
    proof -
      obtain q a b where x: "x = (q, a, b)" by (cases x) auto
      have "map_of l q = Some (a, b)" using that d unfolding x by (simp add: map_of_is_SomeI)
      then show ?thesis unfolding x muF_def by simp
    qed
    then show ?thesis by (simp add: comp_def cong: map_cong)
  qed
  finally show ?thesis .
qed

lemma cert_ok_sound:
  assumes T: "tbl_ok T" and \<psi>: "\<psi> < M" and ok: "cert_ok p T \<Delta> \<psi> l Lam e"
  shows "certificate \<Delta> \<psi> (muF l) (real_of_float Lam) (real_of_float e)"
proof -
  have d: "distinct (map fst l)" and sub: "\<forall>x\<in>set l. inQ \<Delta> (fst x)"
    and L: "upper (rsum p (map (\<lambda>x. sqrt_float_interval p (interval_of (fst (snd x) * fst (snd x) + snd (snd x) * snd (snd x)))) l)) \<le> Lam"
    and E: "upper (rsum p (map (\<lambda>j. cnorm2 p (csub p (T ! \<psi> ! j)
        (csum p (map (\<lambda>x. cmul p (interval_of (fst (snd x)), interval_of (snd (snd x))) (T ! fst x ! j)) l)))) [0..<32])) \<le> e * e"
    using ok unfolding cert_ok_def list_all_iff by blast+
  have qM: "fst x < M" if "x \<in> set l" for x using sub that unfolding inQ_def by blast
  \<comment> \<open>the weights\<close>
  have "(\<Sum>q\<in>Qset \<Delta>. cmod (muF l q)) = sum_list (map (\<lambda>x. cmod (Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x))))) l)"
    using sum_Qset_muF [OF d sub, of "\<lambda>z q. cmod z"] by simp
  also have "\<dots> \<in>\<^sub>r rsum p (map (\<lambda>x. sqrt_float_interval p (interval_of (fst (snd x) * fst (snd x) + snd (snd x) * snd (snd x)))) l)"
  proof (rule rsum_map_in)
    fix x
    have "cmod (Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x))))
        = sqrt (real_of_float (fst (snd x) * fst (snd x) + snd (snd x) * snd (snd x)))"
      by (simp add: complex_norm power2_eq_square)
    then show "cmod (Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x)))) \<in>\<^sub>r sqrt_float_interval p (interval_of (fst (snd x) * fst (snd x) + snd (snd x) * snd (snd x)))"
      by (simp only:) (intro sqrt_float_intervalI interval_of)
  qed
  finally have c1: "(\<Sum>q\<in>Qset \<Delta>. cmod (muF l q)) \<le> real_of_float Lam" using L by (meson upper_in order_trans less_eq_float.rep_eq)
  \<comment> \<open>the residual\<close>
  let ?r = "\<lambda>j. steer ucp (grid \<psi>) j - (\<Sum>q\<in>Qset \<Delta>. muF l q * steer ucp (grid q) j)"
  have r: "?r j = steer ucp (grid \<psi>) j - sum_list (map (\<lambda>x. Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x))) * steer ucp (grid (fst x)) j) l)" for j
    using sum_Qset_muF [OF d sub, of "\<lambda>z q. z * steer ucp (grid q) j"] by simp
  have cin_r: "cin (?r j) (csub p (T ! \<psi> ! j) (csum p (map (\<lambda>x. cmul p (interval_of (fst (snd x)), interval_of (snd (snd x))) (T ! fst x ! j)) l)))"
    if j: "j < 32" for j
    unfolding r
  proof (intro cin_sub cin_sum)
    show "cin (steer ucp (grid \<psi>) j) (T ! \<psi> ! j)" using T \<psi> j unfolding tbl_ok_def by blast
    show "length (map (\<lambda>x. Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x))) * steer ucp (grid (fst x)) j) l)
        = length (map (\<lambda>x. cmul p (interval_of (fst (snd x)), interval_of (snd (snd x))) (T ! fst x ! j)) l)" by simp
    fix i assume "i < length (map (\<lambda>x. Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x))) * steer ucp (grid (fst x)) j) l)"
    then have i: "i < length l" by simp
    then have xin: "l ! i \<in> set l" by simp
    have "cin (Complex (real_of_float (fst (snd (l ! i)))) (real_of_float (snd (snd (l ! i))))) (interval_of (fst (snd (l ! i))), interval_of (snd (snd (l ! i))))"
      by (simp add: cin_def)
    moreover have "cin (steer ucp (grid (fst (l ! i))) j) (T ! fst (l ! i) ! j)" using T qM [OF xin] j unfolding tbl_ok_def by blast
    ultimately show "cin (map (\<lambda>x. Complex (real_of_float (fst (snd x))) (real_of_float (snd (snd x))) * steer ucp (grid (fst x)) j) l ! i)
        (map (\<lambda>x. cmul p (interval_of (fst (snd x)), interval_of (snd (snd x))) (T ! fst x ! j)) l ! i)"
      using i by (simp add: cin_mul)
  qed
  have "(\<Sum>j<32. (cmod (?r j))\<^sup>2) = sum_list (map (\<lambda>j. (cmod (?r j))\<^sup>2) [0..<32])" by (rule sum_lt_list)
  also have "\<dots> \<in>\<^sub>r rsum p (map (\<lambda>j. cnorm2 p (csub p (T ! \<psi> ! j)
        (csum p (map (\<lambda>x. cmul p (interval_of (fst (snd x)), interval_of (snd (snd x))) (T ! fst x ! j)) l)))) [0..<32])"
    by (rule rsum_map_in) (simp add: cin_norm2 cin_r)
  finally have "(\<Sum>j<32. (cmod (?r j))\<^sup>2) \<le> real_of_float (e * e)" using E by (meson upper_in order_trans less_eq_float.rep_eq)
  then have c2: "(\<Sum>j<32. (cmod (?r j))\<^sup>2) \<le> (real_of_float e)\<^sup>2" by (simp add: power2_eq_square)
  show ?thesis unfolding certificate_def using c1 c2 by blast
qed

section \<open>The complete check\<close>

definition EL :: "nat \<Rightarrow> civ list list \<Rightarrow> float list list \<Rightarrow> float \<Rightarrow> float interval list list" where
  "EL p R C s2 = map (\<lambda>i. map (\<lambda>k. EI p R C s2 i k) [0..<64]) [0..<64]"

definition circ_check :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat \<times> float \<times> float) list) list \<Rightarrow> float list list \<Rightarrow>
    float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "circ_check p \<Delta> certs C s2 \<delta> Lam e K =
    (let T = ustL p; E = EL p (map (\<lambda>q. T ! q) (qlist \<Delta>)) C s2 in
      qlist \<Delta> \<noteq> [] \<and>
      list_all (\<lambda>i. sum_list (map (\<lambda>k. upper (abs_interval (E ! i ! k))) [0..<64]) \<le> \<delta>) [0..<64] \<and>
      list_all (\<lambda>k. sum_list (map (\<lambda>i. upper (abs_interval (E ! i ! k))) [0..<64]) \<le> \<delta>) [0..<64] \<and>
      \<delta> < s2 \<and> 0 \<le> e \<and> Lam \<le> K \<and> 1 \<le> K \<and>
      e * e * Float (int (length (qlist \<Delta>))) 0 \<le> (K - Lam) * (K - Lam) * (s2 - \<delta>) \<and>
      list_all (\<lambda>\<psi>. inQ \<Delta> \<psi> \<or> (case map_of certs \<psi> of None \<Rightarrow> False | Some l \<Rightarrow> cert_ok p T \<Delta> \<psi> l Lam e)) [0..<M])"

lemma abs_E_le:
  assumes T: "tbl_ok T" and ik: "i < 64" "k < 64"
  shows "\<bar>Gm \<Delta> i k - LLt (Lf C) i k - (if i = k then real_of_float s2 else 0)\<bar>
      \<le> real_of_float (upper (abs_interval (EL p (map (\<lambda>q. T ! q) (qlist \<Delta>)) C s2 ! i ! k)))"
proof -
  have eq: "EL p (map (\<lambda>q. T ! q) (qlist \<Delta>)) C s2 ! i ! k = EI p (map (\<lambda>q. T ! q) (qlist \<Delta>)) C s2 i k"
    using ik unfolding EL_def by simp
  show ?thesis unfolding eq by (rule upper_in [OF abs_in_float_intervalI [OF EI_in [OF T ik]]])
qed

theorem circ_check_sound:
  assumes chk: "circ_check p \<Delta> certs C s2 \<delta> Lam e K"
  shows "maxAll c \<le> real_of_float K * maxQ \<Delta> c"
    and "(real_of_float s2 - real_of_float \<delta>) * (\<Sum>j<32. (cmod (c j))\<^sup>2) \<le> (\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2)"
    and "real_of_float \<delta> < real_of_float s2"
proof -
  let ?T = "ustL p" let ?E = "EL p (map (\<lambda>q. ?T ! q) (qlist \<Delta>)) C s2"
  let ?Ef = "\<lambda>i k. Gm \<Delta> i k - LLt (Lf C) i k - (if i = k then real_of_float s2 else 0)"
  have T: "tbl_ok ?T" by (rule tbl_ok_ustL)
  from chk have ne: "qlist \<Delta> \<noteq> []"
    and rw: "list_all (\<lambda>i. sum_list (map (\<lambda>k. upper (abs_interval (?E ! i ! k))) [0..<64]) \<le> \<delta>) [0..<64]"
    and cl: "list_all (\<lambda>k. sum_list (map (\<lambda>i. upper (abs_interval (?E ! i ! k))) [0..<64]) \<le> \<delta>) [0..<64]"
    and ds: "\<delta> < s2" and e0: "0 \<le> e" and LK: "Lam \<le> K" and K1: "1 \<le> K"
    and KK: "e * e * Float (int (length (qlist \<Delta>))) 0 \<le> (K - Lam) * (K - Lam) * (s2 - \<delta>)"
    and ce: "list_all (\<lambda>\<psi>. inQ \<Delta> \<psi> \<or> (case map_of certs \<psi> of None \<Rightarrow> False | Some l \<Rightarrow> cert_ok p ?T \<Delta> \<psi> l Lam e)) [0..<M]"
    unfolding circ_check_def Let_def by blast+
  have row: "(\<Sum>k<64. \<bar>?Ef i k\<bar>) \<le> real_of_float \<delta>" if i: "i < 64" for i
  proof -
    have "(\<Sum>k<64. \<bar>?Ef i k\<bar>) \<le> (\<Sum>k<64. real_of_float (upper (abs_interval (?E ! i ! k))))"
      by (rule sum_mono) (rule abs_E_le [OF T i], simp)
    also have "\<dots> = real_of_float (sum_list (map (\<lambda>k. upper (abs_interval (?E ! i ! k))) [0..<64]))"
      unfolding sum_lt_list real_of_float_sum_list map_map comp_def ..
    also have "\<dots> \<le> real_of_float \<delta>"
    proof -
      have "sum_list (map (\<lambda>k. upper (abs_interval (?E ! i ! k))) [0..<64]) \<le> \<delta>"
        using bspec [OF rw [unfolded list_all_iff], of i] i by simp
      then show ?thesis unfolding less_eq_float.rep_eq .
    qed
    finally show ?thesis .
  qed
  have col: "(\<Sum>i<64. \<bar>?Ef i k\<bar>) \<le> real_of_float \<delta>" if k: "k < 64" for k
  proof -
    have "(\<Sum>i<64. \<bar>?Ef i k\<bar>) \<le> (\<Sum>i<64. real_of_float (upper (abs_interval (?E ! i ! k))))"
      by (rule sum_mono) (rule abs_E_le [OF T _ k], simp)
    also have "\<dots> = real_of_float (sum_list (map (\<lambda>i. upper (abs_interval (?E ! i ! k))) [0..<64]))"
      unfolding sum_lt_list real_of_float_sum_list map_map comp_def ..
    also have "\<dots> \<le> real_of_float \<delta>"
    proof -
      have "sum_list (map (\<lambda>i. upper (abs_interval (?E ! i ! k))) [0..<64]) \<le> \<delta>"
        using bspec [OF cl [unfolded list_all_iff], of k] k by simp
      then show ?thesis unfolding less_eq_float.rep_eq .
    qed
    finally show ?thesis .
  qed
  have Qne: "Qset \<Delta> \<noteq> {}" using ne set_qlist [of \<Delta>] by auto
  have card: "card (Qset \<Delta>) = length (qlist \<Delta>)"
    unfolding set_qlist [symmetric] by (rule distinct_card [OF distinct_qlist])
  have KK': "(real_of_float e)\<^sup>2 * real (card (Qset \<Delta>)) \<le> (real_of_float K - real_of_float Lam)\<^sup>2 * (real_of_float s2 - real_of_float \<delta>)"
    using KK unfolding card less_eq_float.rep_eq by (simp add: power2_eq_square)
  have cert: "\<exists>\<mu>. certificate \<Delta> \<psi> \<mu> (real_of_float Lam) (real_of_float e)" if "\<psi> < M" "\<psi> \<notin> Qset \<Delta>" for \<psi>
  proof -
    have "\<not> inQ \<Delta> \<psi>" using that unfolding Qset_def inQ_def by simp
    with ce that have "case map_of certs \<psi> of None \<Rightarrow> False | Some l \<Rightarrow> cert_ok p ?T \<Delta> \<psi> l Lam e"
      unfolding list_all_iff by auto
    then obtain l where "cert_ok p ?T \<Delta> \<psi> l Lam e" by (cases "map_of certs \<psi>") auto
    from cert_ok_sound [OF T that(1) this] show ?thesis by blast
  qed
  show "maxAll c \<le> real_of_float K * maxQ \<Delta> c"
    by (rule floor_from_certificates [OF Qne row col _ _ _ _ KK' cert])
       (use ds e0 LK K1 in \<open>simp_all add: less_eq_float.rep_eq less_float.rep_eq\<close>)
  show "(real_of_float s2 - real_of_float \<delta>) * (\<Sum>j<32. (cmod (c j))\<^sup>2) \<le> (\<Sum>q\<in>Qset \<Delta>. (cmod (Fc c q))\<^sup>2)"
    by (rule norm_bound [OF row col])
  show "real_of_float \<delta> < real_of_float s2" using ds by (simp add: less_float.rep_eq)
qed

end
