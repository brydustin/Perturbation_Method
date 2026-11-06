theory DCX_c30_062
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0992: "dc_sub dc_b30 992"
  by (dc_eval dc_c30_0992)

lemma dc_c30_0993: "dc_sub dc_b30 993"
  by (dc_eval dc_c30_0993)

lemma dc_c30_0994: "dc_sub dc_b30 994"
  by (dc_eval dc_c30_0994)

lemma dc_c30_0995: "dc_sub dc_b30 995"
  by (dc_eval dc_c30_0995)

lemma dc_c30_0996: "dc_sub dc_b30 996"
  by (dc_eval dc_c30_0996)

lemma dc_c30_0997: "dc_sub dc_b30 997"
  by (dc_eval dc_c30_0997)

lemma dc_c30_0998: "dc_sub dc_b30 998"
  by (dc_eval dc_c30_0998)

lemma dc_c30_0999: "dc_sub dc_b30 999"
  by (dc_eval dc_c30_0999)

lemma dc_c30_1000: "dc_sub dc_b30 1000"
  by (dc_eval dc_c30_1000)

lemma dc_c30_1001: "dc_sub dc_b30 1001"
  by (dc_eval dc_c30_1001)

lemma dc_c30_1002: "dc_sub dc_b30 1002"
  by (dc_eval dc_c30_1002)

lemma dc_c30_1003: "dc_sub dc_b30 1003"
  by (dc_eval dc_c30_1003)

lemma dc_c30_1004: "dc_sub dc_b30 1004"
  by (dc_eval dc_c30_1004)

lemma dc_c30_1005: "dc_sub dc_b30 1005"
  by (dc_eval dc_c30_1005)

lemma dc_c30_1006: "dc_sub dc_b30 1006"
  by (dc_eval dc_c30_1006)

lemma dc_c30_1007: "dc_sub dc_b30 1007"
  by (dc_eval dc_c30_1007)

lemma upt_c30_062: "[992..<1008] = [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]"
  by (simp add: upt_rec)

lemma sec_c30_062: "\<forall>j\<in>{16 * 62..<16 * 62 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 62..<16 * 62 + 16}"
  then have "j \<in> set [992..<1008]" unfolding set_upt by simp
  then have "j \<in> set [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]" unfolding upt_c30_062 .
  then show "dc_sub dc_b30 j" using dc_c30_0992 dc_c30_0993 dc_c30_0994 dc_c30_0995 dc_c30_0996 dc_c30_0997 dc_c30_0998 dc_c30_0999 dc_c30_1000 dc_c30_1001 dc_c30_1002 dc_c30_1003 dc_c30_1004 dc_c30_1005 dc_c30_1006 dc_c30_1007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
