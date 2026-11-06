theory OCX_nc_050
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0800: "oc_sub None 800"
  by (oc_eval oc_nc_0800)

lemma oc_nc_0801: "oc_sub None 801"
  by (oc_eval oc_nc_0801)

lemma oc_nc_0802: "oc_sub None 802"
  by (oc_eval oc_nc_0802)

lemma oc_nc_0803: "oc_sub None 803"
  by (oc_eval oc_nc_0803)

lemma oc_nc_0804: "oc_sub None 804"
  by (oc_eval oc_nc_0804)

lemma oc_nc_0805: "oc_sub None 805"
  by (oc_eval oc_nc_0805)

lemma oc_nc_0806: "oc_sub None 806"
  by (oc_eval oc_nc_0806)

lemma oc_nc_0807: "oc_sub None 807"
  by (oc_eval oc_nc_0807)

lemma oc_nc_0808: "oc_sub None 808"
  by (oc_eval oc_nc_0808)

lemma oc_nc_0809: "oc_sub None 809"
  by (oc_eval oc_nc_0809)

lemma oc_nc_0810: "oc_sub None 810"
  by (oc_eval oc_nc_0810)

lemma oc_nc_0811: "oc_sub None 811"
  by (oc_eval oc_nc_0811)

lemma oc_nc_0812: "oc_sub None 812"
  by (oc_eval oc_nc_0812)

lemma oc_nc_0813: "oc_sub None 813"
  by (oc_eval oc_nc_0813)

lemma oc_nc_0814: "oc_sub None 814"
  by (oc_eval oc_nc_0814)

lemma oc_nc_0815: "oc_sub None 815"
  by (oc_eval oc_nc_0815)

lemma upt_nc_050: "[800..<816] = [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]"
  by (simp add: upt_rec)

lemma sec_nc_050: "\<forall>j\<in>{16 * 50..<16 * 50 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 50..<16 * 50 + 16}"
  then have "j \<in> set [800..<816]" unfolding set_upt by simp
  then have "j \<in> set [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]" unfolding upt_nc_050 .
  then show "oc_sub None j" using oc_nc_0800 oc_nc_0801 oc_nc_0802 oc_nc_0803 oc_nc_0804 oc_nc_0805 oc_nc_0806 oc_nc_0807 oc_nc_0808 oc_nc_0809 oc_nc_0810 oc_nc_0811 oc_nc_0812 oc_nc_0813 oc_nc_0814 oc_nc_0815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
