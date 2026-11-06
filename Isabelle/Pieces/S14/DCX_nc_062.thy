theory DCX_nc_062
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0992: "dc_sub None 992"
  by (dc_eval dc_nc_0992)

lemma dc_nc_0993: "dc_sub None 993"
  by (dc_eval dc_nc_0993)

lemma dc_nc_0994: "dc_sub None 994"
  by (dc_eval dc_nc_0994)

lemma dc_nc_0995: "dc_sub None 995"
  by (dc_eval dc_nc_0995)

lemma dc_nc_0996: "dc_sub None 996"
  by (dc_eval dc_nc_0996)

lemma dc_nc_0997: "dc_sub None 997"
  by (dc_eval dc_nc_0997)

lemma dc_nc_0998: "dc_sub None 998"
  by (dc_eval dc_nc_0998)

lemma dc_nc_0999: "dc_sub None 999"
  by (dc_eval dc_nc_0999)

lemma dc_nc_1000: "dc_sub None 1000"
  by (dc_eval dc_nc_1000)

lemma dc_nc_1001: "dc_sub None 1001"
  by (dc_eval dc_nc_1001)

lemma dc_nc_1002: "dc_sub None 1002"
  by (dc_eval dc_nc_1002)

lemma dc_nc_1003: "dc_sub None 1003"
  by (dc_eval dc_nc_1003)

lemma dc_nc_1004: "dc_sub None 1004"
  by (dc_eval dc_nc_1004)

lemma dc_nc_1005: "dc_sub None 1005"
  by (dc_eval dc_nc_1005)

lemma dc_nc_1006: "dc_sub None 1006"
  by (dc_eval dc_nc_1006)

lemma dc_nc_1007: "dc_sub None 1007"
  by (dc_eval dc_nc_1007)

lemma upt_nc_062: "[992..<1008] = [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]"
  by (simp add: upt_rec)

lemma sec_nc_062: "\<forall>j\<in>{16 * 62..<16 * 62 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 62..<16 * 62 + 16}"
  then have "j \<in> set [992..<1008]" unfolding set_upt by simp
  then have "j \<in> set [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]" unfolding upt_nc_062 .
  then show "dc_sub None j" using dc_nc_0992 dc_nc_0993 dc_nc_0994 dc_nc_0995 dc_nc_0996 dc_nc_0997 dc_nc_0998 dc_nc_0999 dc_nc_1000 dc_nc_1001 dc_nc_1002 dc_nc_1003 dc_nc_1004 dc_nc_1005 dc_nc_1006 dc_nc_1007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
