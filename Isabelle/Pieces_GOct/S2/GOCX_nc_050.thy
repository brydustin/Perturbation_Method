theory GOCX_nc_050
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0800: "goc_sub None 800"
  by (goc_eval goc_nc_0800)

lemma goc_nc_0801: "goc_sub None 801"
  by (goc_eval goc_nc_0801)

lemma goc_nc_0802: "goc_sub None 802"
  by (goc_eval goc_nc_0802)

lemma goc_nc_0803: "goc_sub None 803"
  by (goc_eval goc_nc_0803)

lemma goc_nc_0804: "goc_sub None 804"
  by (goc_eval goc_nc_0804)

lemma goc_nc_0805: "goc_sub None 805"
  by (goc_eval goc_nc_0805)

lemma goc_nc_0806: "goc_sub None 806"
  by (goc_eval goc_nc_0806)

lemma goc_nc_0807: "goc_sub None 807"
  by (goc_eval goc_nc_0807)

lemma goc_nc_0808: "goc_sub None 808"
  by (goc_eval goc_nc_0808)

lemma goc_nc_0809: "goc_sub None 809"
  by (goc_eval goc_nc_0809)

lemma goc_nc_0810: "goc_sub None 810"
  by (goc_eval goc_nc_0810)

lemma goc_nc_0811: "goc_sub None 811"
  by (goc_eval goc_nc_0811)

lemma goc_nc_0812: "goc_sub None 812"
  by (goc_eval goc_nc_0812)

lemma goc_nc_0813: "goc_sub None 813"
  by (goc_eval goc_nc_0813)

lemma goc_nc_0814: "goc_sub None 814"
  by (goc_eval goc_nc_0814)

lemma goc_nc_0815: "goc_sub None 815"
  by (goc_eval goc_nc_0815)

lemma gupt_nc_050: "[800..<816] = [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]"
  by (simp add: upt_rec)

lemma gsec_nc_050: "\<forall>j\<in>{16 * 50..<16 * 50 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 50..<16 * 50 + 16}"
  then have "j \<in> set [800..<816]" unfolding set_upt by simp
  then have "j \<in> set [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]" unfolding gupt_nc_050 .
  then show "goc_sub None j" using goc_nc_0800 goc_nc_0801 goc_nc_0802 goc_nc_0803 goc_nc_0804 goc_nc_0805 goc_nc_0806 goc_nc_0807 goc_nc_0808 goc_nc_0809 goc_nc_0810 goc_nc_0811 goc_nc_0812 goc_nc_0813 goc_nc_0814 goc_nc_0815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
