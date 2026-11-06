theory GOCX_nc_002
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0032: "goc_sub None 32"
  by (goc_eval goc_nc_0032)

lemma goc_nc_0033: "goc_sub None 33"
  by (goc_eval goc_nc_0033)

lemma goc_nc_0034: "goc_sub None 34"
  by (goc_eval goc_nc_0034)

lemma goc_nc_0035: "goc_sub None 35"
  by (goc_eval goc_nc_0035)

lemma goc_nc_0036: "goc_sub None 36"
  by (goc_eval goc_nc_0036)

lemma goc_nc_0037: "goc_sub None 37"
  by (goc_eval goc_nc_0037)

lemma goc_nc_0038: "goc_sub None 38"
  by (goc_eval goc_nc_0038)

lemma goc_nc_0039: "goc_sub None 39"
  by (goc_eval goc_nc_0039)

lemma goc_nc_0040: "goc_sub None 40"
  by (goc_eval goc_nc_0040)

lemma goc_nc_0041: "goc_sub None 41"
  by (goc_eval goc_nc_0041)

lemma goc_nc_0042: "goc_sub None 42"
  by (goc_eval goc_nc_0042)

lemma goc_nc_0043: "goc_sub None 43"
  by (goc_eval goc_nc_0043)

lemma goc_nc_0044: "goc_sub None 44"
  by (goc_eval goc_nc_0044)

lemma goc_nc_0045: "goc_sub None 45"
  by (goc_eval goc_nc_0045)

lemma goc_nc_0046: "goc_sub None 46"
  by (goc_eval goc_nc_0046)

lemma goc_nc_0047: "goc_sub None 47"
  by (goc_eval goc_nc_0047)

lemma gupt_nc_002: "[32..<48] = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]"
  by (simp add: upt_rec)

lemma gsec_nc_002: "\<forall>j\<in>{16 * 2..<16 * 2 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 2..<16 * 2 + 16}"
  then have "j \<in> set [32..<48]" unfolding set_upt by simp
  then have "j \<in> set [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]" unfolding gupt_nc_002 .
  then show "goc_sub None j" using goc_nc_0032 goc_nc_0033 goc_nc_0034 goc_nc_0035 goc_nc_0036 goc_nc_0037 goc_nc_0038 goc_nc_0039 goc_nc_0040 goc_nc_0041 goc_nc_0042 goc_nc_0043 goc_nc_0044 goc_nc_0045 goc_nc_0046 goc_nc_0047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
