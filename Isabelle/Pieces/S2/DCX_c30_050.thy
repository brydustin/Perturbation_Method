theory DCX_c30_050
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0800: "dc_sub dc_b30 800"
  by (dc_eval dc_c30_0800)

lemma dc_c30_0801: "dc_sub dc_b30 801"
  by (dc_eval dc_c30_0801)

lemma dc_c30_0802: "dc_sub dc_b30 802"
  by (dc_eval dc_c30_0802)

lemma dc_c30_0803: "dc_sub dc_b30 803"
  by (dc_eval dc_c30_0803)

lemma dc_c30_0804: "dc_sub dc_b30 804"
  by (dc_eval dc_c30_0804)

lemma dc_c30_0805: "dc_sub dc_b30 805"
  by (dc_eval dc_c30_0805)

lemma dc_c30_0806: "dc_sub dc_b30 806"
  by (dc_eval dc_c30_0806)

lemma dc_c30_0807: "dc_sub dc_b30 807"
  by (dc_eval dc_c30_0807)

lemma dc_c30_0808: "dc_sub dc_b30 808"
  by (dc_eval dc_c30_0808)

lemma dc_c30_0809: "dc_sub dc_b30 809"
  by (dc_eval dc_c30_0809)

lemma dc_c30_0810: "dc_sub dc_b30 810"
  by (dc_eval dc_c30_0810)

lemma dc_c30_0811: "dc_sub dc_b30 811"
  by (dc_eval dc_c30_0811)

lemma dc_c30_0812: "dc_sub dc_b30 812"
  by (dc_eval dc_c30_0812)

lemma dc_c30_0813: "dc_sub dc_b30 813"
  by (dc_eval dc_c30_0813)

lemma dc_c30_0814: "dc_sub dc_b30 814"
  by (dc_eval dc_c30_0814)

lemma dc_c30_0815: "dc_sub dc_b30 815"
  by (dc_eval dc_c30_0815)

lemma upt_c30_050: "[800..<816] = [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]"
  by (simp add: upt_rec)

lemma sec_c30_050: "\<forall>j\<in>{16 * 50..<16 * 50 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 50..<16 * 50 + 16}"
  then have "j \<in> set [800..<816]" unfolding set_upt by simp
  then have "j \<in> set [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]" unfolding upt_c30_050 .
  then show "dc_sub dc_b30 j" using dc_c30_0800 dc_c30_0801 dc_c30_0802 dc_c30_0803 dc_c30_0804 dc_c30_0805 dc_c30_0806 dc_c30_0807 dc_c30_0808 dc_c30_0809 dc_c30_0810 dc_c30_0811 dc_c30_0812 dc_c30_0813 dc_c30_0814 dc_c30_0815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
