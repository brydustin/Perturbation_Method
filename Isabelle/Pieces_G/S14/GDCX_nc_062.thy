theory GDCX_nc_062
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0992: "gdc_sub None 992"
  by (gdc_eval gdc_nc_0992)

lemma gdc_nc_0993: "gdc_sub None 993"
  by (gdc_eval gdc_nc_0993)

lemma gdc_nc_0994: "gdc_sub None 994"
  by (gdc_eval gdc_nc_0994)

lemma gdc_nc_0995: "gdc_sub None 995"
  by (gdc_eval gdc_nc_0995)

lemma gdc_nc_0996: "gdc_sub None 996"
  by (gdc_eval gdc_nc_0996)

lemma gdc_nc_0997: "gdc_sub None 997"
  by (gdc_eval gdc_nc_0997)

lemma gdc_nc_0998: "gdc_sub None 998"
  by (gdc_eval gdc_nc_0998)

lemma gdc_nc_0999: "gdc_sub None 999"
  by (gdc_eval gdc_nc_0999)

lemma gdc_nc_1000: "gdc_sub None 1000"
  by (gdc_eval gdc_nc_1000)

lemma gdc_nc_1001: "gdc_sub None 1001"
  by (gdc_eval gdc_nc_1001)

lemma gdc_nc_1002: "gdc_sub None 1002"
  by (gdc_eval gdc_nc_1002)

lemma gdc_nc_1003: "gdc_sub None 1003"
  by (gdc_eval gdc_nc_1003)

lemma gdc_nc_1004: "gdc_sub None 1004"
  by (gdc_eval gdc_nc_1004)

lemma gdc_nc_1005: "gdc_sub None 1005"
  by (gdc_eval gdc_nc_1005)

lemma gdc_nc_1006: "gdc_sub None 1006"
  by (gdc_eval gdc_nc_1006)

lemma gdc_nc_1007: "gdc_sub None 1007"
  by (gdc_eval gdc_nc_1007)

lemma gupt_nc_062: "[992..<1008] = [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]"
  by (simp add: upt_rec)

lemma gsec_nc_062: "\<forall>j\<in>{16 * 62..<16 * 62 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 62..<16 * 62 + 16}"
  then have "j \<in> set [992..<1008]" unfolding set_upt by simp
  then have "j \<in> set [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]" unfolding gupt_nc_062 .
  then show "gdc_sub None j" using gdc_nc_0992 gdc_nc_0993 gdc_nc_0994 gdc_nc_0995 gdc_nc_0996 gdc_nc_0997 gdc_nc_0998 gdc_nc_0999 gdc_nc_1000 gdc_nc_1001 gdc_nc_1002 gdc_nc_1003 gdc_nc_1004 gdc_nc_1005 gdc_nc_1006 gdc_nc_1007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
