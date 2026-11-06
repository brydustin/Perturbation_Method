theory GC_Octagon
  imports GC_Exec GC_Symmetry "Perturbative_Termination.Double_Cross_Symmetry" "Perturbative_Termination.Double_Cross"
    "Sidelobe_Guarantee.G_Guarantee"
begin

text \<open>The octagon: centre element, axis elements at \<open>\<plusminus>a\<close> and diagonal elements at \<open>(\<plusminus>b, \<plusminus>b)\<close>,
  \<open>a\<close> the double nearest 0.0488 m and \<open>b\<close> the double nearest \<open>a/\<surd>2\<close>, in the element order of the double
  cross.  The array is exactly symmetric under rotation by \<open>\<pi>/2\<close> and reflection in the diagonal, so
  the argument below reduces every focus angle to \<open>[0, \<pi>/4]\<close>.  The positions and symmetry lemmas
  are copied from \<open>Pieces_Oct/Tables/Octagon_Symmetry\<close>; the rest is for the changed method.\<close>

definition octagon_d4_pos :: "(float \<times> float) list" where
  "octagon_d4_pos = [(Float 0 0, Float 0 0), (Float (-7032821178101767) (-57), Float 0 0),
    (Float 7032821178101767 (-57), Float 0 0), (Float 0 0, Float 7032821178101767 (-57)),
    (Float 0 0, Float (-7032821178101767) (-57)), (Float 1243238886477031 (-55), Float 1243238886477031 (-55)),
    (Float (-1243238886477031) (-55), Float 1243238886477031 (-55)),
    (Float (-1243238886477031) (-55), Float (-1243238886477031) (-55)),
    (Float 1243238886477031 (-55), Float (-1243238886477031) (-55))]"

definition ocd_q :: "nat \<Rightarrow> float \<times> float" where "ocd_q j = octagon_d4_pos ! j"

section \<open>The octagon and its three generating symmetries\<close>

definition oc_a :: real where "oc_a = real_of_float (Float 7032821178101767 (-57))"
definition oc_b :: real where "oc_b = real_of_float (Float 1243238886477031 (-55))"

abbreviation ocp :: "nat \<Rightarrow> real \<times> real" where "ocp \<equiv> fpos ocd_q"

lemma ocp_simps:
  "ocp 0 = (0, 0)" "ocp 1 = (- oc_a, 0)" "ocp (Suc 0) = (- oc_a, 0)" "ocp 2 = (oc_a, 0)" "ocp 3 = (0, oc_a)" "ocp 4 = (0, - oc_a)"
  "ocp 5 = (oc_b, oc_b)" "ocp 6 = (- oc_b, oc_b)" "ocp 7 = (- oc_b, - oc_b)" "ocp 8 = (oc_b, - oc_b)"
  unfolding fpos_def ocd_q_def octagon_d4_pos_def oc_a_def oc_b_def by simp_all

lemma lessThan9_oc: "{..<9::nat} = {0, 1, 2, 3, 4, 5, 6, 7, 8}"
  by (auto simp: numeral_eq_Suc less_Suc_eq)

lemma lt9_oc: "j < 9 \<Longrightarrow> j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4 \<or> j = 5 \<or> j = 6 \<or> j = 7 \<or> j = (8::nat)"
proof -
  assume "j < 9"
  then have "j \<in> {..<9}" by simp
  then show ?thesis unfolding lessThan9_oc by simp
qed

text \<open>Rotation by \<open>+\<pi>/2\<close>, rotation by \<open>-\<pi>/2\<close>, reflection in the diagonal.\<close>

definition rot_pi_oc :: "nat \<Rightarrow> nat" where "rot_pi_oc j = [0, 3, 4, 2, 1, 8, 5, 6, 7] ! j"
definition rot_g_oc :: "nat \<Rightarrow> nat" where "rot_g_oc m = (if m < 750 then m + 250 else m - 750)"
definition roti_pi_oc :: "nat \<Rightarrow> nat" where "roti_pi_oc j = [0, 4, 3, 1, 2, 6, 7, 8, 5] ! j"
definition roti_g_oc :: "nat \<Rightarrow> nat" where "roti_g_oc m = (if m < 250 then m + 750 else m - 250)"
definition diag_pi_oc :: "nat \<Rightarrow> nat" where "diag_pi_oc j = [0, 4, 3, 2, 1, 5, 8, 7, 6] ! j"
definition diag_g_oc :: "nat \<Rightarrow> nat" where "diag_g_oc m = (if m \<le> 250 then 250 - m else 1250 - m)"

lemma rot_pi_bij_oc: "bij_betw rot_pi_oc {..<9} {..<9}"
  unfolding lessThan9_oc bij_betw_def rot_pi_oc_def by (simp add: inj_on_def insert_commute)

lemma roti_pi_bij_oc: "bij_betw roti_pi_oc {..<9} {..<9}"
  unfolding lessThan9_oc bij_betw_def roti_pi_oc_def by (simp add: inj_on_def insert_commute)

lemma diag_pi_bij_oc: "bij_betw diag_pi_oc {..<9} {..<9}"
  unfolding lessThan9_oc bij_betw_def diag_pi_oc_def by (simp add: inj_on_def insert_commute)

lemma bij_betw_M_oc:
  assumes inv: "\<And>m. m < M \<Longrightarrow> g' (g m) = m" and lt: "\<And>m. m < M \<Longrightarrow> g m < M"
  shows "bij_betw g {..<M} {..<M}"
proof -
  have inj: "inj_on g {..<M}" by (rule inj_on_inverseI [of _ g']) (simp add: inv)
  have "g ` {..<M} = {..<M}" by (rule endo_inj_surj) (auto simp: lt inj)
  then show ?thesis unfolding bij_betw_def using inj by simp
qed

lemma rot_g_bij_oc: "bij_betw rot_g_oc {..<M} {..<M}"
  by (rule bij_betw_M_oc [of roti_g_oc]) (auto simp: rot_g_oc_def roti_g_oc_def M_def)

lemma roti_g_bij_oc: "bij_betw roti_g_oc {..<M} {..<M}"
  by (rule bij_betw_M_oc [of rot_g_oc]) (auto simp: rot_g_oc_def roti_g_oc_def M_def)

lemma diag_g_bij_oc: "bij_betw diag_g_oc {..<M} {..<M}"
  by (rule bij_betw_M_oc [of diag_g_oc]) (auto simp: diag_g_oc_def M_def)

subsection \<open>H1: the element permutations\<close>

lemma rot_H1_oc: "j < 9 \<Longrightarrow> steer ocp (\<phi> + pi/2) j = steer ocp \<phi> (rot_pi_oc j)"
proof -
  assume "j < 9"
  have c: "cos (\<phi> + pi/2) = - sin \<phi>" "sin (\<phi> + pi/2) = cos \<phi>" by (simp_all add: cos_add sin_add)
  from lt9_oc [OF \<open>j < 9\<close>] show ?thesis unfolding steer_def c
    by (elim disjE) (simp_all add: rot_pi_oc_def ocp_simps algebra_simps)
qed

lemma roti_H1_oc: "j < 9 \<Longrightarrow> steer ocp (\<phi> - pi/2) j = steer ocp \<phi> (roti_pi_oc j)"
proof -
  assume "j < 9"
  have c: "cos (\<phi> - pi/2) = sin \<phi>" "sin (\<phi> - pi/2) = - cos \<phi>" by (simp_all add: cos_diff sin_diff)
  from lt9_oc [OF \<open>j < 9\<close>] show ?thesis unfolding steer_def c
    by (elim disjE) (simp_all add: roti_pi_oc_def ocp_simps algebra_simps)
qed

lemma diag_H1_oc: "j < 9 \<Longrightarrow> steer ocp (pi/2 - \<phi>) j = steer ocp \<phi> (diag_pi_oc j)"
proof -
  assume "j < 9"
  have c: "cos (pi/2 - \<phi>) = sin \<phi>" "sin (pi/2 - \<phi>) = cos \<phi>" by (simp_all add: cos_diff sin_diff)
  from lt9_oc [OF \<open>j < 9\<close>] show ?thesis unfolding steer_def c
    by (elim disjE) (simp_all add: diag_pi_oc_def ocp_simps algebra_simps)
qed

subsection \<open>H2 and H4: the grid maps\<close>

lemma grid_rot_oc: "m < M \<Longrightarrow> grid (rot_g_oc m) = (grid m + pi/2) + 2 * pi * of_int (if m < 750 then 0 else - 1)"
  unfolding rot_g_oc_def grid_def M_def by (cases "m < 750") (simp_all add: of_nat_diff field_simps)

lemma grid_roti_oc: "m < M \<Longrightarrow> grid (roti_g_oc m) = (grid m - pi/2) + 2 * pi * of_int (if m < 250 then 1 else 0)"
  unfolding roti_g_oc_def grid_def M_def by (cases "m < 250") (simp_all add: of_nat_diff field_simps)

lemma grid_diag_oc: "m < M \<Longrightarrow> grid (diag_g_oc m) = (pi/2 - grid m) + 2 * pi * of_int (if m \<le> 250 then 0 else 1)"
  unfolding diag_g_oc_def grid_def M_def by (cases "m \<le> 250") (simp_all add: of_nat_diff field_simps)

lemma rot_H2_oc: "m < M \<Longrightarrow> steer ocp (grid (rot_g_oc m)) j = steer ocp (grid m + pi/2) j"
  by (simp only: grid_rot_oc steer_shift)

lemma roti_H2_oc: "m < M \<Longrightarrow> steer ocp (grid (roti_g_oc m)) j = steer ocp (grid m - pi/2) j"
  by (simp only: grid_roti_oc steer_shift)

lemma diag_H2_oc: "m < M \<Longrightarrow> steer ocp (grid (diag_g_oc m)) j = steer ocp (pi/2 - grid m) j"
  by (simp only: grid_diag_oc steer_shift)

lemma rot_H4_oc: "m < M \<Longrightarrow> cdist (grid (rot_g_oc m)) (t + pi/2) = cdist (grid m) t"
  by (simp only: grid_rot_oc cdist_shift cdist_add)

lemma roti_H4_oc: "m < M \<Longrightarrow> cdist (grid (roti_g_oc m)) (t - pi/2) = cdist (grid m) t"
  by (simp only: grid_roti_oc cdist_shift cdist_diff)

lemma diag_H4_oc: "m < M \<Longrightarrow> cdist (grid (diag_g_oc m)) (pi/2 - t) = cdist (grid m) t"
  by (simp only: grid_diag_oc cdist_shift cdist_sub_left)

subsection \<open>H3: neighbours\<close>

lemma rot_H3_eval_oc: "\<forall>m < M. rot_g_oc (prev_idx m) = prev_idx (rot_g_oc m) \<and> rot_g_oc (next_idx m) = next_idx (rot_g_oc m)"
  by eval

lemma roti_H3_eval_oc: "\<forall>m < M. roti_g_oc (prev_idx m) = prev_idx (roti_g_oc m) \<and> roti_g_oc (next_idx m) = next_idx (roti_g_oc m)"
  by eval

lemma diag_H3_eval_oc: "\<forall>m < M. diag_g_oc (prev_idx m) = next_idx (diag_g_oc m) \<and> diag_g_oc (next_idx m) = prev_idx (diag_g_oc m)"
  by eval

lemma rot_H3_oc: "m < M \<Longrightarrow> {rot_g_oc (prev_idx m), rot_g_oc (next_idx m)} = {prev_idx (rot_g_oc m), next_idx (rot_g_oc m)}"
  using rot_H3_eval_oc by simp

lemma roti_H3_oc: "m < M \<Longrightarrow> {roti_g_oc (prev_idx m), roti_g_oc (next_idx m)} = {prev_idx (roti_g_oc m), next_idx (roti_g_oc m)}"
  using roti_H3_eval_oc by simp

lemma diag_H3_oc: "m < M \<Longrightarrow> {diag_g_oc (prev_idx m), diag_g_oc (next_idx m)} = {prev_idx (diag_g_oc m), next_idx (diag_g_oc m)}"
  using diag_H3_eval_oc by (simp add: insert_commute)

subsection \<open>The transport theorems\<close>

section \<open>The changed method on the octagon\<close>

text \<open>The margin \<open>dl = 9/512\<close>; it covers \<open>2 N\<^sup>2 (G + 2 G\<^sup>2) h\<^sup>2 / 8\<close> with \<open>G = 3.067\<close>.\<close>
definition oc_dlf :: float where "oc_dlf = Float 9 (-9)"

lemma oc_dlf_val: "real_of_float oc_dlf = 9 / 512"
  by (simp add: oc_dlf_def powr_minus_divide)

lemmas goc_rot = gall_rules_transport [OF rot_pi_bij_oc rot_g_bij_oc rot_H1_oc rot_H2_oc rot_H3_oc rot_H4_oc]
lemmas goc_roti = gall_rules_transport [OF roti_pi_bij_oc roti_g_bij_oc roti_H1_oc roti_H2_oc roti_H3_oc roti_H4_oc]
lemmas goc_diag = gall_rules_transport [OF diag_pi_bij_oc diag_g_bij_oc diag_H1_oc diag_H2_oc diag_H3_oc diag_H4_oc]

definition goc_stops :: "real option \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "goc_stops bd t D \<longleftrightarrow> (\<forall>tm ts. tie_rule tm ts \<longrightarrow> gstops_within ocp 9 (real_of_float oc_dlf) bd tm ts t D)"

lemma goc_stops_rot: "goc_stops bd t D \<Longrightarrow> goc_stops bd (t + pi/2) D"
  unfolding goc_stops_def using goc_rot by blast

lemma goc_stops_roti: "goc_stops bd t D \<Longrightarrow> goc_stops bd (t - pi/2) D"
  unfolding goc_stops_def using goc_roti by blast

lemma goc_stops_diag: "goc_stops bd t D \<Longrightarrow> goc_stops bd (pi/2 - t) D"
  unfolding goc_stops_def using goc_diag by blast

lemma goc_stops_rot_n: "goc_stops bd t D \<Longrightarrow> goc_stops bd (t + real n * (pi/2)) D"
proof (induction n)
  case (Suc n)
  have eq: "t + real (Suc n) * (pi/2) = (t + real n * (pi/2)) + pi/2" by (simp add: field_simps)
  show ?case unfolding eq by (rule goc_stops_rot [OF Suc.IH [OF Suc.prems]])
qed simp

lemma goc_stops_roti_n: "goc_stops bd t D \<Longrightarrow> goc_stops bd (t - real n * (pi/2)) D"
proof (induction n)
  case (Suc n)
  have eq: "t - real (Suc n) * (pi/2) = (t - real n * (pi/2)) - pi/2" by (simp add: field_simps)
  show ?case unfolding eq by (rule goc_stops_roti [OF Suc.IH [OF Suc.prems]])
qed simp

lemma goc_stops_quarter:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> goc_stops bd t D" and t: "0 \<le> t" "t \<le> pi/2"
  shows "goc_stops bd t D"
proof (cases "t \<le> pi/4")
  case True then show ?thesis using base t by simp
next
  case False
  have "goc_stops bd (pi/2 - t) D" using base [of "pi/2 - t"] False t by simp
  from goc_stops_diag [OF this] show ?thesis by simp
qed

theorem goc_stops_all:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> goc_stops bd t D"
  shows "goc_stops bd t D"
proof -
  define z where "z = \<lfloor>t / (pi/2)\<rfloor>"
  define t0 where "t0 = t - of_int z * (pi/2)"
  have fc: "of_int z \<le> t / (pi/2)" "t / (pi/2) < of_int z + 1"
    unfolding z_def using floor_correct [of "t / (pi/2)"] by simp_all
  have l: "of_int z * (pi/2) \<le> t" by (rule pos_le_divide_eq [THEN iffD1, OF pi_half_gt_zero fc(1)])
  have u: "t < (of_int z + 1) * (pi/2)" by (rule pos_divide_less_eq [THEN iffD1, OF pi_half_gt_zero fc(2)])
  have "(of_int z + 1) * (pi/2) = of_int z * (pi/2) + pi/2" by (simp add: ring_distribs)
  with l u have t0: "0 \<le> t0" "t0 \<le> pi/2" unfolding t0_def by linarith+
  have s0: "goc_stops bd t0 D" by (rule goc_stops_quarter [OF base t0])
  have t_eq: "t = t0 + of_int z * (pi/2)" by (simp add: t0_def)
  show ?thesis
  proof (cases "0 \<le> z")
    case True
    then have "z = int (nat z)" by simp
    then have "t = t0 + real (nat z) * (pi/2)" using t_eq by (metis of_int_of_nat_eq)
    then show ?thesis using goc_stops_rot_n [OF s0, of "nat z"] by simp
  next
    case False
    then have "z = - int (nat (- z))" by simp
    then have "t = t0 - real (nat (- z)) * (pi/2)" using t_eq by (metis of_int_minus of_int_of_nat_eq mult_minus_left diff_conv_add_uminus)
    then show ?thesis using goc_stops_roti_n [OF s0, of "nat (- z)"] by simp
  qed
qed

theorem goc_terminates:
  assumes bd: "band_in bd band" and n: "0 < n"
    and cover: "pi/4 \<le> real_of_float (Float (int n) e)"
    and chk: "\<And>k. k < n \<Longrightarrow> gcheck_sector prec oc_dlf ocd_q 9 inv9_ivl band Dmax wmin f (Float (int k) e) (Float (int k + 1) e)"
    and tr: "tie_rule tm ts"
  shows "gstops_within ocp 9 (real_of_float oc_dlf) bd tm ts t Dmax"
proof -
  have base: "goc_stops bd t Dmax" if "0 \<le> t" "t \<le> pi/4" for t
    unfolding goc_stops_def
  proof (intro allI impI)
    fix tm ts assume tr: "tie_rule tm ts"
    have h: "0 < real_of_float (Float 1 e)" by simp
    have "t \<le> real n * real_of_float (Float 1 e)" using that(2) cover unfolding Float_nat_e by linarith
    from sectors_cover [OF that(1) this h n] obtain k
      where k: "k < n" "real k * real_of_float (Float 1 e) \<le> t" "t \<le> (real k + 1) * real_of_float (Float 1 e)" .
    have lo: "real_of_float (Float (int k) e) \<le> t" using k(2) by simp
    have hi: "t \<le> real_of_float (Float (int k + 1) e)" using k(3) by (simp add: ring_distribs)
    show "gstops_within ocp 9 (real_of_float oc_dlf) bd tm ts t Dmax"
      by (rule gcheck_sector_sound [OF inv9_in bd tr chk [OF k(1)] lo hi])
  qed
  have "goc_stops bd t Dmax" by (rule goc_stops_all) (rule base)
  then show ?thesis unfolding goc_stops_def using tr by blast
qed

section \<open>The margin covers the curvature of the octagon\<close>

lemma oc_ab: "oc_a = 7032821178101767 / 2 ^ 57" "oc_b = 1243238886477031 / 2 ^ 55"
  by (simp_all add: oc_a_def oc_b_def powr_minus_divide powr_realpow)

lemma oc_r2: "j < 9 \<Longrightarrow> (fst (ocp j))\<^sup>2 + (snd (ocp j))\<^sup>2 \<le> (4881 / 100000)\<^sup>2"
proof -
  assume "j < 9"
  then consider "j = 0" | "j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4" | "j = 5 \<or> j = 6 \<or> j = 7 \<or> j = 8" by (auto dest: lt9_oc)
  then show ?thesis
  proof cases
    case 1 then show ?thesis by (simp add: ocp_simps)
  next
    case 2
    have "oc_a\<^sup>2 \<le> (4881 / 100000)\<^sup>2" unfolding oc_ab by (simp add: power2_eq_square divide_simps)
    with 2 show ?thesis by (auto simp: ocp_simps)
  next
    case 3
    have "oc_b\<^sup>2 + oc_b\<^sup>2 \<le> (4881 / 100000)\<^sup>2" unfolding oc_ab by (simp add: power2_eq_square divide_simps)
    with 3 show ?thesis by (auto simp: ocp_simps)
  qed
qed

lemma oc_gam: "j < 9 \<Longrightarrow> gam ocp j \<le> 3067 / 1000"
proof -
  assume j: "j < 9"
  have "sqrt ((fst (ocp j))\<^sup>2 + (snd (ocp j))\<^sup>2) \<le> sqrt ((4881 / 100000)\<^sup>2)"
    by (rule real_sqrt_le_mono [OF oc_r2 [OF j]])
  then have s: "sqrt ((fst (ocp j))\<^sup>2 + (snd (ocp j))\<^sup>2) \<le> 4881 / 100000" by simp
  have "kw \<le> 20 * 3.141592653591" using pi_approx by (simp add: kw_def)
  then have "kw * sqrt ((fst (ocp j))\<^sup>2 + (snd (ocp j))\<^sup>2) \<le> (20 * 3.141592653591) * (4881 / 100000)"
    using s kw_pos by (intro mult_mono) auto
  also have "\<dots> \<le> 3067 / 1000" by simp
  finally show ?thesis by (simp add: gam_def)
qed

lemma oc_dl_ok: "2 * (real 9)\<^sup>2 * (3067 / 1000 + 2 * (3067 / 1000)\<^sup>2) * hM\<^sup>2 / 8 \<le> real_of_float oc_dlf"
proof -
  have h: "hM \<le> 2 * 3.141592653591 / 1000" using pi_approx by (simp add: hM_def M_def)
  have "hM\<^sup>2 \<le> (2 * 3.141592653591 / 1000)\<^sup>2" by (rule power_mono [OF h]) (use hM_pos in simp)
  then have "2 * (real 9)\<^sup>2 * (3067 / 1000 + 2 * (3067 / 1000)\<^sup>2) * hM\<^sup>2 / 8
      \<le> 2 * (real 9)\<^sup>2 * (3067 / 1000 + 2 * (3067 / 1000)\<^sup>2) * (2 * 3.141592653591 / 1000)\<^sup>2 / 8"
    by (intro divide_right_mono mult_left_mono) auto
  also have "\<dots> \<le> 9 / 512" by (simp add: power2_eq_square divide_simps)
  finally show ?thesis by (simp add: oc_dlf_val)
qed

text \<open>For the octagon, stopping within \<open>D\<close> implies the guarantee at the stop.\<close>
theorem goc_guarantee:
  assumes "gstops_within ocp 9 (real_of_float oc_dlf) bd tm ts t D" "tie_rule tm ts"
  shows "\<exists>n \<le> D. gelig ocp 9 (real_of_float oc_dlf) bd tm (grun ocp 9 (real_of_float oc_dlf) bd tm ts t n) t = {} \<and>
           (\<forall>\<phi>. pw ocp 9 (grun ocp 9 (real_of_float oc_dlf) bd tm ts t n) \<phi> > sqmax ocp 9 (grun ocp 9 (real_of_float oc_dlf) bd tm ts t n) / 100 \<longrightarrow>
              (\<exists>q y. lift q y \<and> (q = tm (fmains ocp 9 (grun ocp 9 (real_of_float oc_dlf) bd tm ts t n) t) mod M \<or> (q < M \<and> \<not> in_band bd t q))
                 \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow>
                      pw ocp 9 (grun ocp 9 (real_of_float oc_dlf) bd tm ts t n) \<theta>
                        > sqmax ocp 9 (grun ocp 9 (real_of_float oc_dlf) bd tm ts t n) / 100 - 2 * real_of_float oc_dlf)))"
  by (rule gstops_guarantee [OF assms oc_gam oc_dl_ok])

end
