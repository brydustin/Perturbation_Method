theory Double_Cross_Symmetry
  imports Symmetry Double_Cross
begin

section \<open>Circular distance under shifts and reflections\<close>

lemma abs_cong_eq: "x = y \<Longrightarrow> \<bar>x\<bar> = \<bar>y::real\<bar>" by simp

lemma cdist_cong:
  assumes "(a - b) - (a' - b') = 2 * pi * of_int k"
  shows "cdist a b = cdist a' b'"
proof (rule antisym)
  have "cdist a b \<le> \<bar>(a - b) - 2 * pi * of_int (round ((a' - b') / (2 * pi)) + k)\<bar>" by (rule cdist_min)
  also have "\<dots> = cdist a' b'" unfolding cdist_def of_int_add
    by (rule abs_cong_eq) (use assms in algebra)
  finally show "cdist a b \<le> cdist a' b'" .
  have "cdist a' b' \<le> \<bar>(a' - b') - 2 * pi * of_int (round ((a - b) / (2 * pi)) - k)\<bar>" by (rule cdist_min)
  also have "\<dots> = cdist a b" unfolding cdist_def of_int_diff
    by (rule abs_cong_eq) (use assms in algebra)
  finally show "cdist a' b' \<le> cdist a b" .
qed

lemma cdist_shift: "cdist (a + 2 * pi * of_int k) b = cdist a b"
  by (rule cdist_cong [of _ _ _ _ k]) simp

lemma cdist_add: "cdist (a + d) (b + d) = cdist a b"
  by (rule cdist_cong [of _ _ _ _ 0]) simp

lemma cdist_diff: "cdist (a - d) (b - d) = cdist a b"
  by (rule cdist_cong [of _ _ _ _ 0]) simp

lemma cdist_neg: "cdist (- a) (- b) = cdist a b"
proof (rule antisym)
  let ?r = "round ((a - b) / (2 * pi))"
  have "cdist (- a) (- b) \<le> \<bar>(- a - - b) - 2 * pi * of_int (- ?r)\<bar>" by (rule cdist_min)
  also have "(- a - - b) - 2 * pi * of_int (- ?r) = - ((a - b) - 2 * pi * of_int ?r)" by (simp add: algebra_simps)
  also have "\<bar>- ((a - b) - 2 * pi * of_int ?r)\<bar> = cdist a b" unfolding cdist_def by (rule abs_minus_cancel)
  finally show "cdist (- a) (- b) \<le> cdist a b" .
  let ?r' = "round ((- a - - b) / (2 * pi))"
  have "cdist a b \<le> \<bar>(a - b) - 2 * pi * of_int (- ?r')\<bar>" by (rule cdist_min)
  also have "(a - b) - 2 * pi * of_int (- ?r') = - ((- a - - b) - 2 * pi * of_int ?r')" by (simp add: algebra_simps)
  also have "\<bar>- ((- a - - b) - 2 * pi * of_int ?r')\<bar> = cdist (- a) (- b)" unfolding cdist_def by (rule abs_minus_cancel)
  finally show "cdist a b \<le> cdist (- a) (- b)" .
qed

lemma cdist_sub_left: "cdist (d - a) (d - b) = cdist a b"
proof -
  have "cdist (d - a) (d - b) = cdist (- a) (- b)" by (rule cdist_cong [of _ _ _ _ 0]) simp
  then show ?thesis by (simp only: cdist_neg)
qed

lemma steer_shift: "steer p (\<phi> + 2 * pi * of_int k) j = steer p \<phi> j"
proof -
  have "sin (\<phi> + 2 * pi * of_int k) = sin \<phi> \<and> cos (\<phi> + 2 * pi * of_int k) = cos \<phi>"
    using sin_cos_eq_iff [of "\<phi> + 2 * pi * of_int k" \<phi>] by blast
  then show ?thesis unfolding steer_def by simp
qed

section \<open>The double cross and its three generating symmetries\<close>

definition dc_a :: real where "dc_a = real_of_float (Float 3041648138404103 (-56))"
definition dc_b :: real where "dc_b = real_of_float (Float 5645503481367791 (-57))"

abbreviation dcp :: "nat \<Rightarrow> real \<times> real" where "dcp \<equiv> fpos dc_q"

lemma dcp_simps:
  "dcp 0 = (0, 0)" "dcp 1 = (- dc_a, 0)" "dcp (Suc 0) = (- dc_a, 0)" "dcp 2 = (dc_a, 0)" "dcp 3 = (0, dc_a)" "dcp 4 = (0, - dc_a)"
  "dcp 5 = (dc_b, dc_b)" "dcp 6 = (- dc_b, dc_b)" "dcp 7 = (- dc_b, - dc_b)" "dcp 8 = (dc_b, - dc_b)"
  unfolding fpos_def dc_q_def double_cross_pos_def dc_a_def dc_b_def by simp_all

lemma lessThan9: "{..<9::nat} = {0, 1, 2, 3, 4, 5, 6, 7, 8}"
  by (auto simp: numeral_eq_Suc less_Suc_eq)

lemma lt9: "j < 9 \<Longrightarrow> j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4 \<or> j = 5 \<or> j = 6 \<or> j = 7 \<or> j = (8::nat)"
proof -
  assume "j < 9"
  then have "j \<in> {..<9}" by simp
  then show ?thesis unfolding lessThan9 by simp
qed

text \<open>Rotation by \<open>+\<pi>/2\<close>, rotation by \<open>-\<pi>/2\<close>, reflection in the diagonal.\<close>

definition rot_pi :: "nat \<Rightarrow> nat" where "rot_pi j = [0, 3, 4, 2, 1, 8, 5, 6, 7] ! j"
definition rot_g :: "nat \<Rightarrow> nat" where "rot_g m = (if m < 750 then m + 250 else m - 750)"
definition roti_pi :: "nat \<Rightarrow> nat" where "roti_pi j = [0, 4, 3, 1, 2, 6, 7, 8, 5] ! j"
definition roti_g :: "nat \<Rightarrow> nat" where "roti_g m = (if m < 250 then m + 750 else m - 250)"
definition diag_pi :: "nat \<Rightarrow> nat" where "diag_pi j = [0, 4, 3, 2, 1, 5, 8, 7, 6] ! j"
definition diag_g :: "nat \<Rightarrow> nat" where "diag_g m = (if m \<le> 250 then 250 - m else 1250 - m)"

lemma rot_pi_bij: "bij_betw rot_pi {..<9} {..<9}"
  unfolding lessThan9 bij_betw_def rot_pi_def by (simp add: inj_on_def insert_commute)

lemma roti_pi_bij: "bij_betw roti_pi {..<9} {..<9}"
  unfolding lessThan9 bij_betw_def roti_pi_def by (simp add: inj_on_def insert_commute)

lemma diag_pi_bij: "bij_betw diag_pi {..<9} {..<9}"
  unfolding lessThan9 bij_betw_def diag_pi_def by (simp add: inj_on_def insert_commute)

lemma bij_betw_M:
  assumes inv: "\<And>m. m < M \<Longrightarrow> g' (g m) = m" and lt: "\<And>m. m < M \<Longrightarrow> g m < M"
  shows "bij_betw g {..<M} {..<M}"
proof -
  have inj: "inj_on g {..<M}" by (rule inj_on_inverseI [of _ g']) (simp add: inv)
  have "g ` {..<M} = {..<M}" by (rule endo_inj_surj) (auto simp: lt inj)
  then show ?thesis unfolding bij_betw_def using inj by simp
qed

lemma rot_g_bij: "bij_betw rot_g {..<M} {..<M}"
  by (rule bij_betw_M [of roti_g]) (auto simp: rot_g_def roti_g_def M_def)

lemma roti_g_bij: "bij_betw roti_g {..<M} {..<M}"
  by (rule bij_betw_M [of rot_g]) (auto simp: rot_g_def roti_g_def M_def)

lemma diag_g_bij: "bij_betw diag_g {..<M} {..<M}"
  by (rule bij_betw_M [of diag_g]) (auto simp: diag_g_def M_def)

subsection \<open>H1: the element permutations\<close>

lemma rot_H1: "j < 9 \<Longrightarrow> steer dcp (\<phi> + pi/2) j = steer dcp \<phi> (rot_pi j)"
proof -
  assume "j < 9"
  have c: "cos (\<phi> + pi/2) = - sin \<phi>" "sin (\<phi> + pi/2) = cos \<phi>" by (simp_all add: cos_add sin_add)
  from lt9 [OF \<open>j < 9\<close>] show ?thesis unfolding steer_def c
    by (elim disjE) (simp_all add: rot_pi_def dcp_simps algebra_simps)
qed

lemma roti_H1: "j < 9 \<Longrightarrow> steer dcp (\<phi> - pi/2) j = steer dcp \<phi> (roti_pi j)"
proof -
  assume "j < 9"
  have c: "cos (\<phi> - pi/2) = sin \<phi>" "sin (\<phi> - pi/2) = - cos \<phi>" by (simp_all add: cos_diff sin_diff)
  from lt9 [OF \<open>j < 9\<close>] show ?thesis unfolding steer_def c
    by (elim disjE) (simp_all add: roti_pi_def dcp_simps algebra_simps)
qed

lemma diag_H1: "j < 9 \<Longrightarrow> steer dcp (pi/2 - \<phi>) j = steer dcp \<phi> (diag_pi j)"
proof -
  assume "j < 9"
  have c: "cos (pi/2 - \<phi>) = sin \<phi>" "sin (pi/2 - \<phi>) = cos \<phi>" by (simp_all add: cos_diff sin_diff)
  from lt9 [OF \<open>j < 9\<close>] show ?thesis unfolding steer_def c
    by (elim disjE) (simp_all add: diag_pi_def dcp_simps algebra_simps)
qed

subsection \<open>H2 and H4: the grid maps\<close>

lemma grid_rot: "m < M \<Longrightarrow> grid (rot_g m) = (grid m + pi/2) + 2 * pi * of_int (if m < 750 then 0 else - 1)"
  unfolding rot_g_def grid_def M_def by (cases "m < 750") (simp_all add: of_nat_diff field_simps)

lemma grid_roti: "m < M \<Longrightarrow> grid (roti_g m) = (grid m - pi/2) + 2 * pi * of_int (if m < 250 then 1 else 0)"
  unfolding roti_g_def grid_def M_def by (cases "m < 250") (simp_all add: of_nat_diff field_simps)

lemma grid_diag: "m < M \<Longrightarrow> grid (diag_g m) = (pi/2 - grid m) + 2 * pi * of_int (if m \<le> 250 then 0 else 1)"
  unfolding diag_g_def grid_def M_def by (cases "m \<le> 250") (simp_all add: of_nat_diff field_simps)

lemma rot_H2: "m < M \<Longrightarrow> steer dcp (grid (rot_g m)) j = steer dcp (grid m + pi/2) j"
  by (simp only: grid_rot steer_shift)

lemma roti_H2: "m < M \<Longrightarrow> steer dcp (grid (roti_g m)) j = steer dcp (grid m - pi/2) j"
  by (simp only: grid_roti steer_shift)

lemma diag_H2: "m < M \<Longrightarrow> steer dcp (grid (diag_g m)) j = steer dcp (pi/2 - grid m) j"
  by (simp only: grid_diag steer_shift)

lemma rot_H4: "m < M \<Longrightarrow> cdist (grid (rot_g m)) (t + pi/2) = cdist (grid m) t"
  by (simp only: grid_rot cdist_shift cdist_add)

lemma roti_H4: "m < M \<Longrightarrow> cdist (grid (roti_g m)) (t - pi/2) = cdist (grid m) t"
  by (simp only: grid_roti cdist_shift cdist_diff)

lemma diag_H4: "m < M \<Longrightarrow> cdist (grid (diag_g m)) (pi/2 - t) = cdist (grid m) t"
  by (simp only: grid_diag cdist_shift cdist_sub_left)

subsection \<open>H3: neighbours\<close>

lemma rot_H3_eval: "\<forall>m < M. rot_g (prev_idx m) = prev_idx (rot_g m) \<and> rot_g (next_idx m) = next_idx (rot_g m)"
  by eval

lemma roti_H3_eval: "\<forall>m < M. roti_g (prev_idx m) = prev_idx (roti_g m) \<and> roti_g (next_idx m) = next_idx (roti_g m)"
  by eval

lemma diag_H3_eval: "\<forall>m < M. diag_g (prev_idx m) = next_idx (diag_g m) \<and> diag_g (next_idx m) = prev_idx (diag_g m)"
  by eval

lemma rot_H3: "m < M \<Longrightarrow> {rot_g (prev_idx m), rot_g (next_idx m)} = {prev_idx (rot_g m), next_idx (rot_g m)}"
  using rot_H3_eval by simp

lemma roti_H3: "m < M \<Longrightarrow> {roti_g (prev_idx m), roti_g (next_idx m)} = {prev_idx (roti_g m), next_idx (roti_g m)}"
  using roti_H3_eval by simp

lemma diag_H3: "m < M \<Longrightarrow> {diag_g (prev_idx m), diag_g (next_idx m)} = {prev_idx (diag_g m), next_idx (diag_g m)}"
  using diag_H3_eval by (simp add: insert_commute)

subsection \<open>The transport theorems\<close>

lemmas dc_rot = all_rules_transport [OF rot_pi_bij rot_g_bij rot_H1 rot_H2 rot_H3 rot_H4]
lemmas dc_roti = all_rules_transport [OF roti_pi_bij roti_g_bij roti_H1 roti_H2 roti_H3 roti_H4]
lemmas dc_diag = all_rules_transport [OF diag_pi_bij diag_g_bij diag_H1 diag_H2 diag_H3 diag_H4]

section \<open>Reduction of every focus angle to the sector \<open>[0, \<pi>/4]\<close>\<close>

definition dc_stops :: "real option \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "dc_stops bd t D \<longleftrightarrow> (\<forall>tm ts. tie_rule tm ts \<longrightarrow> stops_within dcp 9 bd tm ts t D)"

lemma dc_stops_rot: "dc_stops bd t D \<Longrightarrow> dc_stops bd (t + pi/2) D"
  unfolding dc_stops_def using dc_rot by blast

lemma dc_stops_roti: "dc_stops bd t D \<Longrightarrow> dc_stops bd (t - pi/2) D"
  unfolding dc_stops_def using dc_roti by blast

lemma dc_stops_diag: "dc_stops bd t D \<Longrightarrow> dc_stops bd (pi/2 - t) D"
  unfolding dc_stops_def using dc_diag by blast

lemma dc_stops_rot_n: "dc_stops bd t D \<Longrightarrow> dc_stops bd (t + real n * (pi/2)) D"
proof (induction n)
  case (Suc n)
  have eq: "t + real (Suc n) * (pi/2) = (t + real n * (pi/2)) + pi/2" by (simp add: field_simps)
  show ?case unfolding eq by (rule dc_stops_rot [OF Suc.IH [OF Suc.prems]])
qed simp

lemma dc_stops_roti_n: "dc_stops bd t D \<Longrightarrow> dc_stops bd (t - real n * (pi/2)) D"
proof (induction n)
  case (Suc n)
  have eq: "t - real (Suc n) * (pi/2) = (t - real n * (pi/2)) - pi/2" by (simp add: field_simps)
  show ?case unfolding eq by (rule dc_stops_roti [OF Suc.IH [OF Suc.prems]])
qed simp

lemma dc_stops_quarter:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> dc_stops bd t D" and t: "0 \<le> t" "t \<le> pi/2"
  shows "dc_stops bd t D"
proof (cases "t \<le> pi/4")
  case True then show ?thesis using base t by simp
next
  case False
  have "dc_stops bd (pi/2 - t) D" using base [of "pi/2 - t"] False t by simp
  from dc_stops_diag [OF this] show ?thesis by simp
qed

theorem dc_stops_all:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> dc_stops bd t D"
  shows "dc_stops bd t D"
proof -
  define z where "z = \<lfloor>t / (pi/2)\<rfloor>"
  define t0 where "t0 = t - of_int z * (pi/2)"
  have fc: "of_int z \<le> t / (pi/2)" "t / (pi/2) < of_int z + 1"
    unfolding z_def using floor_correct [of "t / (pi/2)"] by simp_all
  have l: "of_int z * (pi/2) \<le> t" by (rule pos_le_divide_eq [THEN iffD1, OF pi_half_gt_zero fc(1)])
  have u: "t < (of_int z + 1) * (pi/2)" by (rule pos_divide_less_eq [THEN iffD1, OF pi_half_gt_zero fc(2)])
  have "(of_int z + 1) * (pi/2) = of_int z * (pi/2) + pi/2" by (simp add: ring_distribs)
  with l u have t0: "0 \<le> t0" "t0 \<le> pi/2" unfolding t0_def by linarith+
  have s0: "dc_stops bd t0 D" by (rule dc_stops_quarter [OF base t0])
  have t_eq: "t = t0 + of_int z * (pi/2)" by (simp add: t0_def)
  show ?thesis
  proof (cases "0 \<le> z")
    case True
    then have "z = int (nat z)" by simp
    then have "t = t0 + real (nat z) * (pi/2)" using t_eq by (metis of_int_of_nat_eq)
    then show ?thesis using dc_stops_rot_n [OF s0, of "nat z"] by simp
  next
    case False
    then have "z = - int (nat (- z))" by simp
    then have "t = t0 - real (nat (- z)) * (pi/2)" using t_eq by (metis of_int_minus of_int_of_nat_eq mult_minus_left diff_conv_add_uminus)
    then show ?thesis using dc_stops_roti_n [OF s0, of "nat (- z)"] by simp
  qed
qed

section \<open>From sector checks to the theorem for every focus angle\<close>

text \<open>Uniform sectors \<open>[k h, (k+1) h]\<close>, \<open>h = 2^e\<close>, \<open>k < n\<close>, cover \<open>[0, n h]\<close>.\<close>

lemma Float_nat_e: "real_of_float (Float (int k) e) = real k * real_of_float (Float 1 e)"
  by simp

lemma sectors_cover:
  assumes t: "0 \<le> t" "t \<le> real n * h" and h: "0 < h" and n: "0 < n"
  obtains k where "k < n" "real k * h \<le> t" "t \<le> (real k + 1) * h"
proof -
  define k where "k = min (n - 1) (nat \<lfloor>t / h\<rfloor>)"
  have f0: "0 \<le> \<lfloor>t / h\<rfloor>" using t h by simp
  have fl: "of_int \<lfloor>t / h\<rfloor> \<le> t / h" "t / h < of_int \<lfloor>t / h\<rfloor> + 1" using floor_correct [of "t / h"] by simp_all
  have fl': "of_int \<lfloor>t / h\<rfloor> * h \<le> t" "t < (of_int \<lfloor>t / h\<rfloor> + 1) * h"
    by (rule pos_le_divide_eq [THEN iffD1, OF h fl(1)]) (rule pos_divide_less_eq [THEN iffD1, OF h fl(2)])
  have kn: "k < n" unfolding k_def using n by simp
  have lo: "real k * h \<le> t"
  proof (cases "nat \<lfloor>t / h\<rfloor> \<le> n - 1")
    case True
    then have "k = nat \<lfloor>t / h\<rfloor>" unfolding k_def by simp
    then show ?thesis using fl'(1) f0 by simp
  next
    case False
    then have k: "k = n - 1" unfolding k_def by simp
    have "real (n - 1) \<le> of_int \<lfloor>t / h\<rfloor>" using False f0 by linarith
    then have mono: "real (n - 1) * h \<le> of_int \<lfloor>t / h\<rfloor> * h" by (rule mult_right_mono) (use h in simp)
    show ?thesis unfolding k using mono fl'(1) by linarith
  qed
  have hi: "t \<le> (real k + 1) * h"
  proof (cases "nat \<lfloor>t / h\<rfloor> \<le> n - 1")
    case True
    then have "k = nat \<lfloor>t / h\<rfloor>" unfolding k_def by simp
    then show ?thesis using fl'(2) f0 by simp
  next
    case False
    then have k: "k = n - 1" unfolding k_def by simp
    have eq: "real k + 1 = real n" unfolding k using n by (simp add: of_nat_diff)
    show ?thesis unfolding eq by (rule t(2))
  qed
  from kn lo hi show thesis ..
qed

theorem double_cross_terminates:
  assumes bd: "band_in bd band" and n: "0 < n"
    and cover: "pi/4 \<le> real_of_float (Float (int n) e)"
    and chk: "\<And>k. k < n \<Longrightarrow> check_sector prec dc_q 9 inv9_ivl band Dmax wmin f (Float (int k) e) (Float (int k + 1) e)"
    and tr: "tie_rule tm ts"
  shows "stops_within dcp 9 bd tm ts t Dmax"
proof -
  have base: "dc_stops bd t Dmax" if "0 \<le> t" "t \<le> pi/4" for t
    unfolding dc_stops_def
  proof (intro allI impI)
    fix tm ts assume tr: "tie_rule tm ts"
    have h: "0 < real_of_float (Float 1 e)" by simp
    have "t \<le> real n * real_of_float (Float 1 e)" using that(2) cover unfolding Float_nat_e by linarith
    from sectors_cover [OF that(1) this h n] obtain k
      where k: "k < n" "real k * real_of_float (Float 1 e) \<le> t" "t \<le> (real k + 1) * real_of_float (Float 1 e)" .
    have lo: "real_of_float (Float (int k) e) \<le> t" using k(2) by simp
    have hi: "t \<le> real_of_float (Float (int k + 1) e)" using k(3) by (simp add: ring_distribs)
    show "stops_within dcp 9 bd tm ts t Dmax"
      by (rule check_sector_sound [OF inv9_in bd tr chk [OF k(1)] lo hi])
  qed
  have "dc_stops bd t Dmax" by (rule dc_stops_all) (rule base)
  then show ?thesis unfolding dc_stops_def using tr by blast
qed

end
