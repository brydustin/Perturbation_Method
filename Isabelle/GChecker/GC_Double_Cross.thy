theory GC_Double_Cross
  imports GC_Exec GC_Symmetry "Perturbative_Termination.Double_Cross_Symmetry" "Perturbative_Termination.Double_Cross"
    "Sidelobe_Guarantee.G_Guarantee"
begin

section \<open>The changed method on the double cross\<close>

text \<open>The margin \<open>dl = 23/1024\<close>; it covers \<open>2 N\<^sup>2 (G + 2 G\<^sup>2) h\<^sup>2 / 8\<close> with \<open>G = 7/2\<close>.\<close>
definition dc_dlf :: float where "dc_dlf = Float 23 (-10)"

lemma dc_dlf_val: "real_of_float dc_dlf = 23 / 1024"
  by (simp add: dc_dlf_def powr_minus_divide)

lemmas gdc_rot = gall_rules_transport [OF rot_pi_bij rot_g_bij rot_H1 rot_H2 rot_H3 rot_H4]
lemmas gdc_roti = gall_rules_transport [OF roti_pi_bij roti_g_bij roti_H1 roti_H2 roti_H3 roti_H4]
lemmas gdc_diag = gall_rules_transport [OF diag_pi_bij diag_g_bij diag_H1 diag_H2 diag_H3 diag_H4]

definition gdc_stops :: "real option \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "gdc_stops bd t D \<longleftrightarrow> (\<forall>tm ts. tie_rule tm ts \<longrightarrow> gstops_within dcp 9 (real_of_float dc_dlf) bd tm ts t D)"

lemma gdc_stops_rot: "gdc_stops bd t D \<Longrightarrow> gdc_stops bd (t + pi/2) D"
  unfolding gdc_stops_def using gdc_rot by blast

lemma gdc_stops_roti: "gdc_stops bd t D \<Longrightarrow> gdc_stops bd (t - pi/2) D"
  unfolding gdc_stops_def using gdc_roti by blast

lemma gdc_stops_diag: "gdc_stops bd t D \<Longrightarrow> gdc_stops bd (pi/2 - t) D"
  unfolding gdc_stops_def using gdc_diag by blast

lemma gdc_stops_rot_n: "gdc_stops bd t D \<Longrightarrow> gdc_stops bd (t + real n * (pi/2)) D"
proof (induction n)
  case (Suc n)
  have eq: "t + real (Suc n) * (pi/2) = (t + real n * (pi/2)) + pi/2" by (simp add: field_simps)
  show ?case unfolding eq by (rule gdc_stops_rot [OF Suc.IH [OF Suc.prems]])
qed simp

lemma gdc_stops_roti_n: "gdc_stops bd t D \<Longrightarrow> gdc_stops bd (t - real n * (pi/2)) D"
proof (induction n)
  case (Suc n)
  have eq: "t - real (Suc n) * (pi/2) = (t - real n * (pi/2)) - pi/2" by (simp add: field_simps)
  show ?case unfolding eq by (rule gdc_stops_roti [OF Suc.IH [OF Suc.prems]])
qed simp

lemma gdc_stops_quarter:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> gdc_stops bd t D" and t: "0 \<le> t" "t \<le> pi/2"
  shows "gdc_stops bd t D"
proof (cases "t \<le> pi/4")
  case True then show ?thesis using base t by simp
next
  case False
  have "gdc_stops bd (pi/2 - t) D" using base [of "pi/2 - t"] False t by simp
  from gdc_stops_diag [OF this] show ?thesis by simp
qed

theorem gdc_stops_all:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> gdc_stops bd t D"
  shows "gdc_stops bd t D"
proof -
  define z where "z = \<lfloor>t / (pi/2)\<rfloor>"
  define t0 where "t0 = t - of_int z * (pi/2)"
  have fc: "of_int z \<le> t / (pi/2)" "t / (pi/2) < of_int z + 1"
    unfolding z_def using floor_correct [of "t / (pi/2)"] by simp_all
  have l: "of_int z * (pi/2) \<le> t" by (rule pos_le_divide_eq [THEN iffD1, OF pi_half_gt_zero fc(1)])
  have u: "t < (of_int z + 1) * (pi/2)" by (rule pos_divide_less_eq [THEN iffD1, OF pi_half_gt_zero fc(2)])
  have "(of_int z + 1) * (pi/2) = of_int z * (pi/2) + pi/2" by (simp add: ring_distribs)
  with l u have t0: "0 \<le> t0" "t0 \<le> pi/2" unfolding t0_def by linarith+
  have s0: "gdc_stops bd t0 D" by (rule gdc_stops_quarter [OF base t0])
  have t_eq: "t = t0 + of_int z * (pi/2)" by (simp add: t0_def)
  show ?thesis
  proof (cases "0 \<le> z")
    case True
    then have "z = int (nat z)" by simp
    then have "t = t0 + real (nat z) * (pi/2)" using t_eq by (metis of_int_of_nat_eq)
    then show ?thesis using gdc_stops_rot_n [OF s0, of "nat z"] by simp
  next
    case False
    then have "z = - int (nat (- z))" by simp
    then have "t = t0 - real (nat (- z)) * (pi/2)" using t_eq by (metis of_int_minus of_int_of_nat_eq mult_minus_left diff_conv_add_uminus)
    then show ?thesis using gdc_stops_roti_n [OF s0, of "nat (- z)"] by simp
  qed
qed

text \<open>From checks of the uniform sectors \<open>[k 2\<^sup>e, (k+1) 2\<^sup>e]\<close>, \<open>k < n\<close>, covering \<open>[0, \<pi>/4]\<close>, to every focus.\<close>
theorem gdc_terminates:
  assumes bd: "band_in bd band" and n: "0 < n"
    and cover: "pi/4 \<le> real_of_float (Float (int n) e)"
    and chk: "\<And>k. k < n \<Longrightarrow> gcheck_sector prec dc_dlf dc_q 9 inv9_ivl band Dmax wmin f (Float (int k) e) (Float (int k + 1) e)"
    and tr: "tie_rule tm ts"
  shows "gstops_within dcp 9 (real_of_float dc_dlf) bd tm ts t Dmax"
proof -
  have base: "gdc_stops bd t Dmax" if "0 \<le> t" "t \<le> pi/4" for t
    unfolding gdc_stops_def
  proof (intro allI impI)
    fix tm ts assume tr: "tie_rule tm ts"
    have h: "0 < real_of_float (Float 1 e)" by simp
    have "t \<le> real n * real_of_float (Float 1 e)" using that(2) cover unfolding Float_nat_e by linarith
    from sectors_cover [OF that(1) this h n] obtain k
      where k: "k < n" "real k * real_of_float (Float 1 e) \<le> t" "t \<le> (real k + 1) * real_of_float (Float 1 e)" .
    have lo: "real_of_float (Float (int k) e) \<le> t" using k(2) by simp
    have hi: "t \<le> real_of_float (Float (int k + 1) e)" using k(3) by (simp add: ring_distribs)
    show "gstops_within dcp 9 (real_of_float dc_dlf) bd tm ts t Dmax"
      by (rule gcheck_sector_sound [OF inv9_in bd tr chk [OF k(1)] lo hi])
  qed
  have "gdc_stops bd t Dmax" by (rule gdc_stops_all) (rule base)
  then show ?thesis unfolding gdc_stops_def using tr by blast
qed

section \<open>The margin covers the curvature of the double cross\<close>

lemma dc_ab: "dc_a = 3041648138404103 / 2 ^ 56" "dc_b = 5645503481367791 / 2 ^ 57"
  by (simp_all add: dc_a_def dc_b_def powr_minus_divide powr_realpow)

lemma dc_r2: "j < 9 \<Longrightarrow> (fst (dcp j))\<^sup>2 + (snd (dcp j))\<^sup>2 \<le> (555 / 10000)\<^sup>2"
proof -
  assume "j < 9"
  then consider "j = 0" | "j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4" | "j = 5 \<or> j = 6 \<or> j = 7 \<or> j = 8" by (auto dest: lt9)
  then show ?thesis
  proof cases
    case 1 then show ?thesis by (simp add: dcp_simps)
  next
    case 2
    have "dc_a\<^sup>2 \<le> (555 / 10000)\<^sup>2" unfolding dc_ab by simp
    with 2 show ?thesis by (auto simp: dcp_simps)
  next
    case 3
    have "dc_b\<^sup>2 + dc_b\<^sup>2 \<le> (555 / 10000)\<^sup>2" unfolding dc_ab by (simp add: power2_eq_square divide_simps)
    with 3 show ?thesis by (auto simp: dcp_simps)
  qed
qed

lemma dc_gam: "j < 9 \<Longrightarrow> gam dcp j \<le> 7 / 2"
proof -
  assume j: "j < 9"
  have "sqrt ((fst (dcp j))\<^sup>2 + (snd (dcp j))\<^sup>2) \<le> sqrt ((555 / 10000)\<^sup>2)"
    by (rule real_sqrt_le_mono [OF dc_r2 [OF j]])
  then have s: "sqrt ((fst (dcp j))\<^sup>2 + (snd (dcp j))\<^sup>2) \<le> 555 / 10000" by simp
  have "kw \<le> 20 * 3.141592653591" using pi_approx by (simp add: kw_def)
  then have "kw * sqrt ((fst (dcp j))\<^sup>2 + (snd (dcp j))\<^sup>2) \<le> (20 * 3.141592653591) * (555 / 10000)"
    using s kw_pos by (intro mult_mono) auto
  also have "\<dots> \<le> 7 / 2" by simp
  finally show ?thesis by (simp add: gam_def)
qed

lemma dc_dl_ok: "2 * (real 9)\<^sup>2 * (7 / 2 + 2 * (7 / 2)\<^sup>2) * hM\<^sup>2 / 8 \<le> real_of_float dc_dlf"
proof -
  have h: "hM \<le> 2 * 3.141592653591 / 1000" using pi_approx by (simp add: hM_def M_def)
  have "hM\<^sup>2 \<le> (2 * 3.141592653591 / 1000)\<^sup>2" by (rule power_mono [OF h]) (use hM_pos in simp)
  then have "2 * (real 9)\<^sup>2 * (7 / 2 + 2 * (7 / 2)\<^sup>2) * hM\<^sup>2 / 8 \<le> 2 * (real 9)\<^sup>2 * (7 / 2 + 2 * (7 / 2)\<^sup>2) * (2 * 3.141592653591 / 1000)\<^sup>2 / 8"
    by (intro divide_right_mono mult_left_mono) auto
  also have "\<dots> \<le> 23 / 1024" by (simp add: power2_eq_square divide_simps)
  finally show ?thesis by (simp add: dc_dlf_val)
qed

text \<open>For the double cross, stopping within \<open>D\<close> implies the guarantee at the stop.\<close>
theorem gdc_guarantee:
  assumes "gstops_within dcp 9 (real_of_float dc_dlf) bd tm ts t D" "tie_rule tm ts"
  shows "\<exists>n \<le> D. gelig dcp 9 (real_of_float dc_dlf) bd tm (grun dcp 9 (real_of_float dc_dlf) bd tm ts t n) t = {} \<and>
           (\<forall>\<phi>. pw dcp 9 (grun dcp 9 (real_of_float dc_dlf) bd tm ts t n) \<phi> > sqmax dcp 9 (grun dcp 9 (real_of_float dc_dlf) bd tm ts t n) / 100 \<longrightarrow>
              (\<exists>q y. lift q y \<and> (q = tm (fmains dcp 9 (grun dcp 9 (real_of_float dc_dlf) bd tm ts t n) t) mod M \<or> (q < M \<and> \<not> in_band bd t q))
                 \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow>
                      pw dcp 9 (grun dcp 9 (real_of_float dc_dlf) bd tm ts t n) \<theta>
                        > sqmax dcp 9 (grun dcp 9 (real_of_float dc_dlf) bd tm ts t n) / 100 - 2 * real_of_float dc_dlf)))"
  by (rule gstops_guarantee [OF assms dc_gam dc_dl_ok])

end
