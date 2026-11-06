theory DCX_c30_169
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2704: "dc_sub dc_b30 2704"
  by (dc_eval dc_c30_2704)

lemma dc_c30_2705: "dc_sub dc_b30 2705"
  by (dc_eval dc_c30_2705)

lemma dc_c30_2706: "dc_sub dc_b30 2706"
  by (dc_eval dc_c30_2706)

lemma dc_c30_2707: "dc_sub dc_b30 2707"
  by (dc_eval dc_c30_2707)

lemma dc_c30_2708: "dc_sub dc_b30 2708"
  by (dc_eval dc_c30_2708)

lemma dc_c30_2709: "dc_sub dc_b30 2709"
  by (dc_eval dc_c30_2709)

lemma dc_c30_2710: "dc_sub dc_b30 2710"
  by (dc_eval dc_c30_2710)

lemma dc_c30_2711: "dc_sub dc_b30 2711"
  by (dc_eval dc_c30_2711)

lemma dc_c30_2712: "dc_sub dc_b30 2712"
  by (dc_eval dc_c30_2712)

lemma dc_c30_2713: "dc_sub dc_b30 2713"
  by (dc_eval dc_c30_2713)

lemma dc_c30_2714: "dc_sub dc_b30 2714"
  by (dc_eval dc_c30_2714)

lemma dc_c30_2715: "dc_sub dc_b30 2715"
  by (dc_eval dc_c30_2715)

lemma dc_c30_2716: "dc_sub dc_b30 2716"
  by (dc_eval dc_c30_2716)

lemma dc_c30_2717: "dc_sub dc_b30 2717"
  by (dc_eval dc_c30_2717)

lemma dc_c30_2718: "dc_sub dc_b30 2718"
  by (dc_eval dc_c30_2718)

lemma dc_c30_2719: "dc_sub dc_b30 2719"
  by (dc_eval dc_c30_2719)

lemma upt_c30_169: "[2704..<2720] = [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]"
  by (simp add: upt_rec)

lemma sec_c30_169: "\<forall>j\<in>{16 * 169..<16 * 169 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 169..<16 * 169 + 16}"
  then have "j \<in> set [2704..<2720]" unfolding set_upt by simp
  then have "j \<in> set [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]" unfolding upt_c30_169 .
  then show "dc_sub dc_b30 j" using dc_c30_2704 dc_c30_2705 dc_c30_2706 dc_c30_2707 dc_c30_2708 dc_c30_2709 dc_c30_2710 dc_c30_2711 dc_c30_2712 dc_c30_2713 dc_c30_2714 dc_c30_2715 dc_c30_2716 dc_c30_2717 dc_c30_2718 dc_c30_2719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
