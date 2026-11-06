theory DCX_nc_169
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2704: "dc_sub None 2704"
  by (dc_eval dc_nc_2704)

lemma dc_nc_2705: "dc_sub None 2705"
  by (dc_eval dc_nc_2705)

lemma dc_nc_2706: "dc_sub None 2706"
  by (dc_eval dc_nc_2706)

lemma dc_nc_2707: "dc_sub None 2707"
  by (dc_eval dc_nc_2707)

lemma dc_nc_2708: "dc_sub None 2708"
  by (dc_eval dc_nc_2708)

lemma dc_nc_2709: "dc_sub None 2709"
  by (dc_eval dc_nc_2709)

lemma dc_nc_2710: "dc_sub None 2710"
  by (dc_eval dc_nc_2710)

lemma dc_nc_2711: "dc_sub None 2711"
  by (dc_eval dc_nc_2711)

lemma dc_nc_2712: "dc_sub None 2712"
  by (dc_eval dc_nc_2712)

lemma dc_nc_2713: "dc_sub None 2713"
  by (dc_eval dc_nc_2713)

lemma dc_nc_2714: "dc_sub None 2714"
  by (dc_eval dc_nc_2714)

lemma dc_nc_2715: "dc_sub None 2715"
  by (dc_eval dc_nc_2715)

lemma dc_nc_2716: "dc_sub None 2716"
  by (dc_eval dc_nc_2716)

lemma dc_nc_2717: "dc_sub None 2717"
  by (dc_eval dc_nc_2717)

lemma dc_nc_2718: "dc_sub None 2718"
  by (dc_eval dc_nc_2718)

lemma dc_nc_2719: "dc_sub None 2719"
  by (dc_eval dc_nc_2719)

lemma upt_nc_169: "[2704..<2720] = [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]"
  by (simp add: upt_rec)

lemma sec_nc_169: "\<forall>j\<in>{16 * 169..<16 * 169 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 169..<16 * 169 + 16}"
  then have "j \<in> set [2704..<2720]" unfolding set_upt by simp
  then have "j \<in> set [2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719]" unfolding upt_nc_169 .
  then show "dc_sub None j" using dc_nc_2704 dc_nc_2705 dc_nc_2706 dc_nc_2707 dc_nc_2708 dc_nc_2709 dc_nc_2710 dc_nc_2711 dc_nc_2712 dc_nc_2713 dc_nc_2714 dc_nc_2715 dc_nc_2716 dc_nc_2717 dc_nc_2718 dc_nc_2719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
