theory DCX_c30_044
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0704: "dc_sub dc_b30 704"
  by (dc_eval dc_c30_0704)

lemma dc_c30_0705: "dc_sub dc_b30 705"
  by (dc_eval dc_c30_0705)

lemma dc_c30_0706: "dc_sub dc_b30 706"
  by (dc_eval dc_c30_0706)

lemma dc_c30_0707: "dc_sub dc_b30 707"
  by (dc_eval dc_c30_0707)

lemma dc_c30_0708: "dc_sub dc_b30 708"
  by (dc_eval dc_c30_0708)

lemma dc_c30_0709: "dc_sub dc_b30 709"
  by (dc_eval dc_c30_0709)

lemma dc_c30_0710: "dc_sub dc_b30 710"
  by (dc_eval dc_c30_0710)

lemma dc_c30_0711: "dc_sub dc_b30 711"
  by (dc_eval dc_c30_0711)

lemma dc_c30_0712: "dc_sub dc_b30 712"
  by (dc_eval dc_c30_0712)

lemma dc_c30_0713: "dc_sub dc_b30 713"
  by (dc_eval dc_c30_0713)

lemma dc_c30_0714: "dc_sub dc_b30 714"
  by (dc_eval dc_c30_0714)

lemma dc_c30_0715: "dc_sub dc_b30 715"
  by (dc_eval dc_c30_0715)

lemma dc_c30_0716: "dc_sub dc_b30 716"
  by (dc_eval dc_c30_0716)

lemma dc_c30_0717: "dc_sub dc_b30 717"
  by (dc_eval dc_c30_0717)

lemma dc_c30_0718: "dc_sub dc_b30 718"
  by (dc_eval dc_c30_0718)

lemma dc_c30_0719: "dc_sub dc_b30 719"
  by (dc_eval dc_c30_0719)

lemma upt_c30_044: "[704..<720] = [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]"
  by (simp add: upt_rec)

lemma sec_c30_044: "\<forall>j\<in>{16 * 44..<16 * 44 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 44..<16 * 44 + 16}"
  then have "j \<in> set [704..<720]" unfolding set_upt by simp
  then have "j \<in> set [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]" unfolding upt_c30_044 .
  then show "dc_sub dc_b30 j" using dc_c30_0704 dc_c30_0705 dc_c30_0706 dc_c30_0707 dc_c30_0708 dc_c30_0709 dc_c30_0710 dc_c30_0711 dc_c30_0712 dc_c30_0713 dc_c30_0714 dc_c30_0715 dc_c30_0716 dc_c30_0717 dc_c30_0718 dc_c30_0719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
