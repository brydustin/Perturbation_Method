theory OCX_nc_062
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0992: "oc_sub None 992"
  by (oc_eval oc_nc_0992)

lemma oc_nc_0993: "oc_sub None 993"
  by (oc_eval oc_nc_0993)

lemma oc_nc_0994: "oc_sub None 994"
  by (oc_eval oc_nc_0994)

lemma oc_nc_0995: "oc_sub None 995"
  by (oc_eval oc_nc_0995)

lemma oc_nc_0996: "oc_sub None 996"
  by (oc_eval oc_nc_0996)

lemma oc_nc_0997: "oc_sub None 997"
  by (oc_eval oc_nc_0997)

lemma oc_nc_0998: "oc_sub None 998"
  by (oc_eval oc_nc_0998)

lemma oc_nc_0999: "oc_sub None 999"
  by (oc_eval oc_nc_0999)

lemma oc_nc_1000: "oc_sub None 1000"
  by (oc_eval oc_nc_1000)

lemma oc_nc_1001: "oc_sub None 1001"
  by (oc_eval oc_nc_1001)

lemma oc_nc_1002: "oc_sub None 1002"
  by (oc_eval oc_nc_1002)

lemma oc_nc_1003: "oc_sub None 1003"
  by (oc_eval oc_nc_1003)

lemma oc_nc_1004: "oc_sub None 1004"
  by (oc_eval oc_nc_1004)

lemma oc_nc_1005: "oc_sub None 1005"
  by (oc_eval oc_nc_1005)

lemma oc_nc_1006: "oc_sub None 1006"
  by (oc_eval oc_nc_1006)

lemma oc_nc_1007: "oc_sub None 1007"
  by (oc_eval oc_nc_1007)

lemma upt_nc_062: "[992..<1008] = [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]"
  by (simp add: upt_rec)

lemma sec_nc_062: "\<forall>j\<in>{16 * 62..<16 * 62 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 62..<16 * 62 + 16}"
  then have "j \<in> set [992..<1008]" unfolding set_upt by simp
  then have "j \<in> set [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]" unfolding upt_nc_062 .
  then show "oc_sub None j" using oc_nc_0992 oc_nc_0993 oc_nc_0994 oc_nc_0995 oc_nc_0996 oc_nc_0997 oc_nc_0998 oc_nc_0999 oc_nc_1000 oc_nc_1001 oc_nc_1002 oc_nc_1003 oc_nc_1004 oc_nc_1005 oc_nc_1006 oc_nc_1007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
