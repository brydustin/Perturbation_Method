theory GOCX_nc_044
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0704: "goc_sub None 704"
  by (goc_eval goc_nc_0704)

lemma goc_nc_0705: "goc_sub None 705"
  by (goc_eval goc_nc_0705)

lemma goc_nc_0706: "goc_sub None 706"
  by (goc_eval goc_nc_0706)

lemma goc_nc_0707: "goc_sub None 707"
  by (goc_eval goc_nc_0707)

lemma goc_nc_0708: "goc_sub None 708"
  by (goc_eval goc_nc_0708)

lemma goc_nc_0709: "goc_sub None 709"
  by (goc_eval goc_nc_0709)

lemma goc_nc_0710: "goc_sub None 710"
  by (goc_eval goc_nc_0710)

lemma goc_nc_0711: "goc_sub None 711"
  by (goc_eval goc_nc_0711)

lemma goc_nc_0712: "goc_sub None 712"
  by (goc_eval goc_nc_0712)

lemma goc_nc_0713: "goc_sub None 713"
  by (goc_eval goc_nc_0713)

lemma goc_nc_0714: "goc_sub None 714"
  by (goc_eval goc_nc_0714)

lemma goc_nc_0715: "goc_sub None 715"
  by (goc_eval goc_nc_0715)

lemma goc_nc_0716: "goc_sub None 716"
  by (goc_eval goc_nc_0716)

lemma goc_nc_0717: "goc_sub None 717"
  by (goc_eval goc_nc_0717)

lemma goc_nc_0718: "goc_sub None 718"
  by (goc_eval goc_nc_0718)

lemma goc_nc_0719: "goc_sub None 719"
  by (goc_eval goc_nc_0719)

lemma gupt_nc_044: "[704..<720] = [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]"
  by (simp add: upt_rec)

lemma gsec_nc_044: "\<forall>j\<in>{16 * 44..<16 * 44 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 44..<16 * 44 + 16}"
  then have "j \<in> set [704..<720]" unfolding set_upt by simp
  then have "j \<in> set [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]" unfolding gupt_nc_044 .
  then show "goc_sub None j" using goc_nc_0704 goc_nc_0705 goc_nc_0706 goc_nc_0707 goc_nc_0708 goc_nc_0709 goc_nc_0710 goc_nc_0711 goc_nc_0712 goc_nc_0713 goc_nc_0714 goc_nc_0715 goc_nc_0716 goc_nc_0717 goc_nc_0718 goc_nc_0719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
