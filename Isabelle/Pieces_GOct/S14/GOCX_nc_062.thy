theory GOCX_nc_062
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0992: "goc_sub None 992"
  by (goc_eval goc_nc_0992)

lemma goc_nc_0993: "goc_sub None 993"
  by (goc_eval goc_nc_0993)

lemma goc_nc_0994: "goc_sub None 994"
  by (goc_eval goc_nc_0994)

lemma goc_nc_0995: "goc_sub None 995"
  by (goc_eval goc_nc_0995)

lemma goc_nc_0996: "goc_sub None 996"
  by (goc_eval goc_nc_0996)

lemma goc_nc_0997: "goc_sub None 997"
  by (goc_eval goc_nc_0997)

lemma goc_nc_0998: "goc_sub None 998"
  by (goc_eval goc_nc_0998)

lemma goc_nc_0999: "goc_sub None 999"
  by (goc_eval goc_nc_0999)

lemma goc_nc_1000: "goc_sub None 1000"
  by (goc_eval goc_nc_1000)

lemma goc_nc_1001: "goc_sub None 1001"
  by (goc_eval goc_nc_1001)

lemma goc_nc_1002: "goc_sub None 1002"
  by (goc_eval goc_nc_1002)

lemma goc_nc_1003: "goc_sub None 1003"
  by (goc_eval goc_nc_1003)

lemma goc_nc_1004: "goc_sub None 1004"
  by (goc_eval goc_nc_1004)

lemma goc_nc_1005: "goc_sub None 1005"
  by (goc_eval goc_nc_1005)

lemma goc_nc_1006: "goc_sub None 1006"
  by (goc_eval goc_nc_1006)

lemma goc_nc_1007: "goc_sub None 1007"
  by (goc_eval goc_nc_1007)

lemma gupt_nc_062: "[992..<1008] = [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]"
  by (simp add: upt_rec)

lemma gsec_nc_062: "\<forall>j\<in>{16 * 62..<16 * 62 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 62..<16 * 62 + 16}"
  then have "j \<in> set [992..<1008]" unfolding set_upt by simp
  then have "j \<in> set [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]" unfolding gupt_nc_062 .
  then show "goc_sub None j" using goc_nc_0992 goc_nc_0993 goc_nc_0994 goc_nc_0995 goc_nc_0996 goc_nc_0997 goc_nc_0998 goc_nc_0999 goc_nc_1000 goc_nc_1001 goc_nc_1002 goc_nc_1003 goc_nc_1004 goc_nc_1005 goc_nc_1006 goc_nc_1007
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
