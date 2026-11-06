theory OCX_c30_169
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2704: "oc_sub oc_b30 2704"
  by (oc_eval oc_c30_2704)

lemma oc_c30_2705: "oc_sub oc_b30 2705"
  by (oc_eval oc_c30_2705)

lemma oc_c30_2706: "oc_sub oc_b30 2706"
  by (oc_eval oc_c30_2706)

lemma oc_c30_2707: "oc_sub oc_b30 2707"
  by (oc_eval oc_c30_2707)

lemma oc_c30_2708: "oc_sub oc_b30 2708"
  by (oc_eval oc_c30_2708)

lemma oc_c30_2709: "oc_sub oc_b30 2709"
  by (oc_eval oc_c30_2709)

lemma oc_c30_2710: "oc_sub oc_b30 2710"
  by (oc_eval oc_c30_2710)

lemma oc_c30_2711: "oc_sub oc_b30 2711"
  by (oc_eval oc_c30_2711)

lemma oc_c30_2712: "oc_sub oc_b30 2712"
  by (oc_eval oc_c30_2712)

lemma oc_c30_2713: "oc_sub oc_b30 2713"
  by (oc_eval oc_c30_2713)

lemma oc_c30_2714: "oc_sub oc_b30 2714"
  by (oc_eval oc_c30_2714)

lemma oc_c30_2715: "oc_sub oc_b30 2715"
  by (oc_eval oc_c30_2715)

lemma oc_c30_2716: "oc_sub oc_b30 2716"
  by (oc_eval oc_c30_2716)

lemma oc_c30_2717: "oc_sub oc_b30 2717"
  by (oc_eval oc_c30_2717)

lemma oc_c30_2718: "oc_sub oc_b30 2718"
  by (oc_eval oc_c30_2718)

lemma oc_c30_2719: "oc_sub oc_b30 2719"
  by (oc_eval oc_c30_2719)

lemma upt_c30_169: "[2704..<2720] = [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]"
  by (simp add: upt_rec)

lemma sec_c30_169: "\<forall>j\<in>{16 * 169..<16 * 169 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 169..<16 * 169 + 16}"
  then have "j \<in> set [2704..<2720]" unfolding set_upt by simp
  then have "j \<in> set [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]" unfolding upt_c30_169 .
  then show "oc_sub oc_b30 j" using oc_c30_2704 oc_c30_2705 oc_c30_2706 oc_c30_2707 oc_c30_2708 oc_c30_2709 oc_c30_2710 oc_c30_2711 oc_c30_2712 oc_c30_2713 oc_c30_2714 oc_c30_2715 oc_c30_2716 oc_c30_2717 oc_c30_2718 oc_c30_2719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
