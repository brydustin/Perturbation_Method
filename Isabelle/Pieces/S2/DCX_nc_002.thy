theory DCX_nc_002
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0032: "dc_sub None 32"
  by (dc_eval dc_nc_0032)

lemma dc_nc_0033: "dc_sub None 33"
  by (dc_eval dc_nc_0033)

lemma dc_nc_0034: "dc_sub None 34"
  by (dc_eval dc_nc_0034)

lemma dc_nc_0035: "dc_sub None 35"
  by (dc_eval dc_nc_0035)

lemma dc_nc_0036: "dc_sub None 36"
  by (dc_eval dc_nc_0036)

lemma dc_nc_0037: "dc_sub None 37"
  by (dc_eval dc_nc_0037)

lemma dc_nc_0038: "dc_sub None 38"
  by (dc_eval dc_nc_0038)

lemma dc_nc_0039: "dc_sub None 39"
  by (dc_eval dc_nc_0039)

lemma dc_nc_0040: "dc_sub None 40"
  by (dc_eval dc_nc_0040)

lemma dc_nc_0041: "dc_sub None 41"
  by (dc_eval dc_nc_0041)

lemma dc_nc_0042: "dc_sub None 42"
  by (dc_eval dc_nc_0042)

lemma dc_nc_0043: "dc_sub None 43"
  by (dc_eval dc_nc_0043)

lemma dc_nc_0044: "dc_sub None 44"
  by (dc_eval dc_nc_0044)

lemma dc_nc_0045: "dc_sub None 45"
  by (dc_eval dc_nc_0045)

lemma dc_nc_0046: "dc_sub None 46"
  by (dc_eval dc_nc_0046)

lemma dc_nc_0047: "dc_sub None 47"
  by (dc_eval dc_nc_0047)

lemma upt_nc_002: "[32..<48] = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]"
  by (simp add: upt_rec)

lemma sec_nc_002: "\<forall>j\<in>{16 * 2..<16 * 2 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 2..<16 * 2 + 16}"
  then have "j \<in> set [32..<48]" unfolding set_upt by simp
  then have "j \<in> set [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]" unfolding upt_nc_002 .
  then show "dc_sub None j" using dc_nc_0032 dc_nc_0033 dc_nc_0034 dc_nc_0035 dc_nc_0036 dc_nc_0037 dc_nc_0038 dc_nc_0039 dc_nc_0040 dc_nc_0041 dc_nc_0042 dc_nc_0043 dc_nc_0044 dc_nc_0045 dc_nc_0046 dc_nc_0047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
