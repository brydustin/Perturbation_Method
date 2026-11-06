theory GDCX_nc_044
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0704: "gdc_sub None 704"
  by (gdc_eval gdc_nc_0704)

lemma gdc_nc_0705: "gdc_sub None 705"
  by (gdc_eval gdc_nc_0705)

lemma gdc_nc_0706: "gdc_sub None 706"
  by (gdc_eval gdc_nc_0706)

lemma gdc_nc_0707: "gdc_sub None 707"
  by (gdc_eval gdc_nc_0707)

lemma gdc_nc_0708: "gdc_sub None 708"
  by (gdc_eval gdc_nc_0708)

lemma gdc_nc_0709: "gdc_sub None 709"
  by (gdc_eval gdc_nc_0709)

lemma gdc_nc_0710: "gdc_sub None 710"
  by (gdc_eval gdc_nc_0710)

lemma gdc_nc_0711: "gdc_sub None 711"
  by (gdc_eval gdc_nc_0711)

lemma gdc_nc_0712: "gdc_sub None 712"
  by (gdc_eval gdc_nc_0712)

lemma gdc_nc_0713: "gdc_sub None 713"
  by (gdc_eval gdc_nc_0713)

lemma gdc_nc_0714: "gdc_sub None 714"
  by (gdc_eval gdc_nc_0714)

lemma gdc_nc_0715: "gdc_sub None 715"
  by (gdc_eval gdc_nc_0715)

lemma gdc_nc_0716: "gdc_sub None 716"
  by (gdc_eval gdc_nc_0716)

lemma gdc_nc_0717: "gdc_sub None 717"
  by (gdc_eval gdc_nc_0717)

lemma gdc_nc_0718: "gdc_sub None 718"
  by (gdc_eval gdc_nc_0718)

lemma gdc_nc_0719: "gdc_sub None 719"
  by (gdc_eval gdc_nc_0719)

lemma gupt_nc_044: "[704..<720] = [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]"
  by (simp add: upt_rec)

lemma gsec_nc_044: "\<forall>j\<in>{16 * 44..<16 * 44 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 44..<16 * 44 + 16}"
  then have "j \<in> set [704..<720]" unfolding set_upt by simp
  then have "j \<in> set [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]" unfolding gupt_nc_044 .
  then show "gdc_sub None j" using gdc_nc_0704 gdc_nc_0705 gdc_nc_0706 gdc_nc_0707 gdc_nc_0708 gdc_nc_0709 gdc_nc_0710 gdc_nc_0711 gdc_nc_0712 gdc_nc_0713 gdc_nc_0714 gdc_nc_0715 gdc_nc_0716 gdc_nc_0717 gdc_nc_0718 gdc_nc_0719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
