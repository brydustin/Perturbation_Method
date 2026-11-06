theory OCX_nc_044
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0704: "oc_sub None 704"
  by (oc_eval oc_nc_0704)

lemma oc_nc_0705: "oc_sub None 705"
  by (oc_eval oc_nc_0705)

lemma oc_nc_0706: "oc_sub None 706"
  by (oc_eval oc_nc_0706)

lemma oc_nc_0707: "oc_sub None 707"
  by (oc_eval oc_nc_0707)

lemma oc_nc_0708: "oc_sub None 708"
  by (oc_eval oc_nc_0708)

lemma oc_nc_0709: "oc_sub None 709"
  by (oc_eval oc_nc_0709)

lemma oc_nc_0710: "oc_sub None 710"
  by (oc_eval oc_nc_0710)

lemma oc_nc_0711: "oc_sub None 711"
  by (oc_eval oc_nc_0711)

lemma oc_nc_0712: "oc_sub None 712"
  by (oc_eval oc_nc_0712)

lemma oc_nc_0713: "oc_sub None 713"
  by (oc_eval oc_nc_0713)

lemma oc_nc_0714: "oc_sub None 714"
  by (oc_eval oc_nc_0714)

lemma oc_nc_0715: "oc_sub None 715"
  by (oc_eval oc_nc_0715)

lemma oc_nc_0716: "oc_sub None 716"
  by (oc_eval oc_nc_0716)

lemma oc_nc_0717: "oc_sub None 717"
  by (oc_eval oc_nc_0717)

lemma oc_nc_0718: "oc_sub None 718"
  by (oc_eval oc_nc_0718)

lemma oc_nc_0719: "oc_sub None 719"
  by (oc_eval oc_nc_0719)

lemma upt_nc_044: "[704..<720] = [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]"
  by (simp add: upt_rec)

lemma sec_nc_044: "\<forall>j\<in>{16 * 44..<16 * 44 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 44..<16 * 44 + 16}"
  then have "j \<in> set [704..<720]" unfolding set_upt by simp
  then have "j \<in> set [704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719]" unfolding upt_nc_044 .
  then show "oc_sub None j" using oc_nc_0704 oc_nc_0705 oc_nc_0706 oc_nc_0707 oc_nc_0708 oc_nc_0709 oc_nc_0710 oc_nc_0711 oc_nc_0712 oc_nc_0713 oc_nc_0714 oc_nc_0715 oc_nc_0716 oc_nc_0717 oc_nc_0718 oc_nc_0719
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
