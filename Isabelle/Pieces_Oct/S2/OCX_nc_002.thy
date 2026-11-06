theory OCX_nc_002
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0032: "oc_sub None 32"
  by (oc_eval oc_nc_0032)

lemma oc_nc_0033: "oc_sub None 33"
  by (oc_eval oc_nc_0033)

lemma oc_nc_0034: "oc_sub None 34"
  by (oc_eval oc_nc_0034)

lemma oc_nc_0035: "oc_sub None 35"
  by (oc_eval oc_nc_0035)

lemma oc_nc_0036: "oc_sub None 36"
  by (oc_eval oc_nc_0036)

lemma oc_nc_0037: "oc_sub None 37"
  by (oc_eval oc_nc_0037)

lemma oc_nc_0038: "oc_sub None 38"
  by (oc_eval oc_nc_0038)

lemma oc_nc_0039: "oc_sub None 39"
  by (oc_eval oc_nc_0039)

lemma oc_nc_0040: "oc_sub None 40"
  by (oc_eval oc_nc_0040)

lemma oc_nc_0041: "oc_sub None 41"
  by (oc_eval oc_nc_0041)

lemma oc_nc_0042: "oc_sub None 42"
  by (oc_eval oc_nc_0042)

lemma oc_nc_0043: "oc_sub None 43"
  by (oc_eval oc_nc_0043)

lemma oc_nc_0044: "oc_sub None 44"
  by (oc_eval oc_nc_0044)

lemma oc_nc_0045: "oc_sub None 45"
  by (oc_eval oc_nc_0045)

lemma oc_nc_0046: "oc_sub None 46"
  by (oc_eval oc_nc_0046)

lemma oc_nc_0047: "oc_sub None 47"
  by (oc_eval oc_nc_0047)

lemma upt_nc_002: "[32..<48] = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]"
  by (simp add: upt_rec)

lemma sec_nc_002: "\<forall>j\<in>{16 * 2..<16 * 2 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 2..<16 * 2 + 16}"
  then have "j \<in> set [32..<48]" unfolding set_upt by simp
  then have "j \<in> set [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]" unfolding upt_nc_002 .
  then show "oc_sub None j" using oc_nc_0032 oc_nc_0033 oc_nc_0034 oc_nc_0035 oc_nc_0036 oc_nc_0037 oc_nc_0038 oc_nc_0039 oc_nc_0040 oc_nc_0041 oc_nc_0042 oc_nc_0043 oc_nc_0044 oc_nc_0045 oc_nc_0046 oc_nc_0047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
