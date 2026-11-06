theory GDCX_nc_050
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0800: "gdc_sub None 800"
  by (gdc_eval gdc_nc_0800)

lemma gdc_nc_0801: "gdc_sub None 801"
  by (gdc_eval gdc_nc_0801)

lemma gdc_nc_0802: "gdc_sub None 802"
  by (gdc_eval gdc_nc_0802)

lemma gdc_nc_0803: "gdc_sub None 803"
  by (gdc_eval gdc_nc_0803)

lemma gdc_nc_0804: "gdc_sub None 804"
  by (gdc_eval gdc_nc_0804)

lemma gdc_nc_0805: "gdc_sub None 805"
  by (gdc_eval gdc_nc_0805)

lemma gdc_nc_0806: "gdc_sub None 806"
  by (gdc_eval gdc_nc_0806)

lemma gdc_nc_0807: "gdc_sub None 807"
  by (gdc_eval gdc_nc_0807)

lemma gdc_nc_0808: "gdc_sub None 808"
  by (gdc_eval gdc_nc_0808)

lemma gdc_nc_0809: "gdc_sub None 809"
  by (gdc_eval gdc_nc_0809)

lemma gdc_nc_0810: "gdc_sub None 810"
  by (gdc_eval gdc_nc_0810)

lemma gdc_nc_0811: "gdc_sub None 811"
  by (gdc_eval gdc_nc_0811)

lemma gdc_nc_0812: "gdc_sub None 812"
  by (gdc_eval gdc_nc_0812)

lemma gdc_nc_0813: "gdc_sub None 813"
  by (gdc_eval gdc_nc_0813)

lemma gdc_nc_0814: "gdc_sub None 814"
  by (gdc_eval gdc_nc_0814)

lemma gdc_nc_0815: "gdc_sub None 815"
  by (gdc_eval gdc_nc_0815)

lemma gupt_nc_050: "[800..<816] = [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]"
  by (simp add: upt_rec)

lemma gsec_nc_050: "\<forall>j\<in>{16 * 50..<16 * 50 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 50..<16 * 50 + 16}"
  then have "j \<in> set [800..<816]" unfolding set_upt by simp
  then have "j \<in> set [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]" unfolding gupt_nc_050 .
  then show "gdc_sub None j" using gdc_nc_0800 gdc_nc_0801 gdc_nc_0802 gdc_nc_0803 gdc_nc_0804 gdc_nc_0805 gdc_nc_0806 gdc_nc_0807 gdc_nc_0808 gdc_nc_0809 gdc_nc_0810 gdc_nc_0811 gdc_nc_0812 gdc_nc_0813 gdc_nc_0814 gdc_nc_0815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
