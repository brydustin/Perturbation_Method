theory OCX_c30_050
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0800: "oc_sub oc_b30 800"
  by (oc_eval oc_c30_0800)

lemma oc_c30_0801: "oc_sub oc_b30 801"
  by (oc_eval oc_c30_0801)

lemma oc_c30_0802: "oc_sub oc_b30 802"
  by (oc_eval oc_c30_0802)

lemma oc_c30_0803: "oc_sub oc_b30 803"
  by (oc_eval oc_c30_0803)

lemma oc_c30_0804: "oc_sub oc_b30 804"
  by (oc_eval oc_c30_0804)

lemma oc_c30_0805: "oc_sub oc_b30 805"
  by (oc_eval oc_c30_0805)

lemma oc_c30_0806: "oc_sub oc_b30 806"
  by (oc_eval oc_c30_0806)

lemma oc_c30_0807: "oc_sub oc_b30 807"
  by (oc_eval oc_c30_0807)

lemma oc_c30_0808: "oc_sub oc_b30 808"
  by (oc_eval oc_c30_0808)

lemma oc_c30_0809: "oc_sub oc_b30 809"
  by (oc_eval oc_c30_0809)

lemma oc_c30_0810: "oc_sub oc_b30 810"
  by (oc_eval oc_c30_0810)

lemma oc_c30_0811: "oc_sub oc_b30 811"
  by (oc_eval oc_c30_0811)

lemma oc_c30_0812: "oc_sub oc_b30 812"
  by (oc_eval oc_c30_0812)

lemma oc_c30_0813: "oc_sub oc_b30 813"
  by (oc_eval oc_c30_0813)

lemma oc_c30_0814: "oc_sub oc_b30 814"
  by (oc_eval oc_c30_0814)

lemma oc_c30_0815: "oc_sub oc_b30 815"
  by (oc_eval oc_c30_0815)

lemma upt_c30_050: "[800..<816] = [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]"
  by (simp add: upt_rec)

lemma sec_c30_050: "\<forall>j\<in>{16 * 50..<16 * 50 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 50..<16 * 50 + 16}"
  then have "j \<in> set [800..<816]" unfolding set_upt by simp
  then have "j \<in> set [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815]" unfolding upt_c30_050 .
  then show "oc_sub oc_b30 j" using oc_c30_0800 oc_c30_0801 oc_c30_0802 oc_c30_0803 oc_c30_0804 oc_c30_0805 oc_c30_0806 oc_c30_0807 oc_c30_0808 oc_c30_0809 oc_c30_0810 oc_c30_0811 oc_c30_0812 oc_c30_0813 oc_c30_0814 oc_c30_0815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
