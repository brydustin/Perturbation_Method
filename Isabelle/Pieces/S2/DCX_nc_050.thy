theory DCX_nc_050
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0800: "dc_sub None 800"
  by (dc_eval dc_nc_0800)

lemma dc_nc_0801: "dc_sub None 801"
  by (dc_eval dc_nc_0801)

lemma dc_nc_0802: "dc_sub None 802"
  by (dc_eval dc_nc_0802)

lemma dc_nc_0803: "dc_sub None 803"
  by (dc_eval dc_nc_0803)

lemma dc_nc_0804: "dc_sub None 804"
  by (dc_eval dc_nc_0804)

lemma dc_nc_0805: "dc_sub None 805"
  by (dc_eval dc_nc_0805)

lemma dc_nc_0806: "dc_sub None 806"
  by (dc_eval dc_nc_0806)

lemma dc_nc_0807: "dc_sub None 807"
  by (dc_eval dc_nc_0807)

lemma dc_nc_0808: "dc_sub None 808"
  by (dc_eval dc_nc_0808)

lemma dc_nc_0809: "dc_sub None 809"
  by (dc_eval dc_nc_0809)

lemma dc_nc_0810: "dc_sub None 810"
  by (dc_eval dc_nc_0810)

lemma dc_nc_0811: "dc_sub None 811"
  by (dc_eval dc_nc_0811)

lemma dc_nc_0812: "dc_sub None 812"
  by (dc_eval dc_nc_0812)

lemma dc_nc_0813: "dc_sub None 813"
  by (dc_eval dc_nc_0813)

lemma dc_nc_0814: "dc_sub None 814"
  by (dc_eval dc_nc_0814)

lemma dc_nc_0815: "dc_sub None 815"
  by (dc_eval dc_nc_0815)

lemma upt_nc_050: "[800..<816] = [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]"
  by (simp add: upt_rec)

lemma sec_nc_050: "\<forall>j\<in>{16 * 50..<16 * 50 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 50..<16 * 50 + 16}"
  then have "j \<in> set [800..<816]" unfolding set_upt by simp
  then have "j \<in> set [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]" unfolding upt_nc_050 .
  then show "dc_sub None j" using dc_nc_0800 dc_nc_0801 dc_nc_0802 dc_nc_0803 dc_nc_0804 dc_nc_0805 dc_nc_0806 dc_nc_0807 dc_nc_0808 dc_nc_0809 dc_nc_0810 dc_nc_0811 dc_nc_0812 dc_nc_0813 dc_nc_0814 dc_nc_0815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
