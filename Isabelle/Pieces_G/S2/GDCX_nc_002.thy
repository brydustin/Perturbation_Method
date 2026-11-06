theory GDCX_nc_002
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0032: "gdc_sub None 32"
  by (gdc_eval gdc_nc_0032)

lemma gdc_nc_0033: "gdc_sub None 33"
  by (gdc_eval gdc_nc_0033)

lemma gdc_nc_0034: "gdc_sub None 34"
  by (gdc_eval gdc_nc_0034)

lemma gdc_nc_0035: "gdc_sub None 35"
  by (gdc_eval gdc_nc_0035)

lemma gdc_nc_0036: "gdc_sub None 36"
  by (gdc_eval gdc_nc_0036)

lemma gdc_nc_0037: "gdc_sub None 37"
  by (gdc_eval gdc_nc_0037)

lemma gdc_nc_0038: "gdc_sub None 38"
  by (gdc_eval gdc_nc_0038)

lemma gdc_nc_0039: "gdc_sub None 39"
  by (gdc_eval gdc_nc_0039)

lemma gdc_nc_0040: "gdc_sub None 40"
  by (gdc_eval gdc_nc_0040)

lemma gdc_nc_0041: "gdc_sub None 41"
  by (gdc_eval gdc_nc_0041)

lemma gdc_nc_0042: "gdc_sub None 42"
  by (gdc_eval gdc_nc_0042)

lemma gdc_nc_0043: "gdc_sub None 43"
  by (gdc_eval gdc_nc_0043)

lemma gdc_nc_0044: "gdc_sub None 44"
  by (gdc_eval gdc_nc_0044)

lemma gdc_nc_0045: "gdc_sub None 45"
  by (gdc_eval gdc_nc_0045)

lemma gdc_nc_0046: "gdc_sub None 46"
  by (gdc_eval gdc_nc_0046)

lemma gdc_nc_0047: "gdc_sub None 47"
  by (gdc_eval gdc_nc_0047)

lemma gupt_nc_002: "[32..<48] = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]"
  by (simp add: upt_rec)

lemma gsec_nc_002: "\<forall>j\<in>{16 * 2..<16 * 2 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 2..<16 * 2 + 16}"
  then have "j \<in> set [32..<48]" unfolding set_upt by simp
  then have "j \<in> set [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]" unfolding gupt_nc_002 .
  then show "gdc_sub None j" using gdc_nc_0032 gdc_nc_0033 gdc_nc_0034 gdc_nc_0035 gdc_nc_0036 gdc_nc_0037 gdc_nc_0038 gdc_nc_0039 gdc_nc_0040 gdc_nc_0041 gdc_nc_0042 gdc_nc_0043 gdc_nc_0044 gdc_nc_0045 gdc_nc_0046 gdc_nc_0047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
