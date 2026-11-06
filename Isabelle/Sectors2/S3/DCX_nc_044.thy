theory DCX_nc_044
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0704: "dc_sub None 704"
  by (dc_eval dc_nc_0704)

lemma dc_nc_0705: "dc_sub None 705"
  by (dc_eval dc_nc_0705)

lemma dc_nc_0706: "dc_sub None 706"
  by (dc_eval dc_nc_0706)

lemma dc_nc_0707: "dc_sub None 707"
  by (dc_eval dc_nc_0707)

lemma dc_nc_0708: "dc_sub None 708"
  by (dc_eval dc_nc_0708)

lemma dc_nc_0709: "dc_sub None 709"
  by (dc_eval dc_nc_0709)

lemma dc_nc_0710: "dc_sub None 710"
  by (dc_eval dc_nc_0710)

lemma dc_nc_0711: "dc_sub None 711"
  by (dc_eval dc_nc_0711)

lemma dc_nc_0712: "dc_sub None 712"
  by (dc_eval dc_nc_0712)

lemma dc_nc_0713: "dc_sub None 713"
  by (dc_eval dc_nc_0713)

lemma dc_nc_0714: "dc_sub None 714"
  by (dc_eval dc_nc_0714)

lemma dc_nc_0715: "dc_sub None 715"
  by (dc_eval dc_nc_0715)

lemma dc_nc_0716: "dc_sub None 716"
  by (dc_eval dc_nc_0716)

lemma dc_nc_0717: "dc_sub None 717"
  by (dc_eval dc_nc_0717)

lemma dc_nc_0718: "dc_sub None 718"
  by (dc_eval dc_nc_0718)

lemma dc_nc_0719: "dc_sub None 719"
  by (dc_eval dc_nc_0719)

lemma upt_nc_044: "[704..<720] = [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]"
  by (simp add: upt_rec)

lemma sec_nc_044: "\<forall>j\<in>{16 * 44..<16 * 44 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 44..<16 * 44 + 16}"
  then have "j \<in> set [704..<720]" unfolding set_upt by simp
  then have "j \<in> set [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]" unfolding upt_nc_044 .
  then show "dc_sub None j" using dc_nc_0704 dc_nc_0705 dc_nc_0706 dc_nc_0707 dc_nc_0708 dc_nc_0709 dc_nc_0710 dc_nc_0711 dc_nc_0712 dc_nc_0713 dc_nc_0714 dc_nc_0715 dc_nc_0716 dc_nc_0717 dc_nc_0718 dc_nc_0719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
