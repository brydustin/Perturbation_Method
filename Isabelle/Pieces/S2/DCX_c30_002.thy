theory DCX_c30_002
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0032: "dc_sub dc_b30 32"
  by (dc_eval dc_c30_0032)

lemma dc_c30_0033: "dc_sub dc_b30 33"
  by (dc_eval dc_c30_0033)

lemma dc_c30_0034: "dc_sub dc_b30 34"
  by (dc_eval dc_c30_0034)

lemma dc_c30_0035: "dc_sub dc_b30 35"
  by (dc_eval dc_c30_0035)

lemma dc_c30_0036: "dc_sub dc_b30 36"
  by (dc_eval dc_c30_0036)

lemma dc_c30_0037: "dc_sub dc_b30 37"
  by (dc_eval dc_c30_0037)

lemma dc_c30_0038: "dc_sub dc_b30 38"
  by (dc_eval dc_c30_0038)

lemma dc_c30_0039: "dc_sub dc_b30 39"
  by (dc_eval dc_c30_0039)

lemma dc_c30_0040: "dc_sub dc_b30 40"
  by (dc_eval dc_c30_0040)

lemma dc_c30_0041: "dc_sub dc_b30 41"
  by (dc_eval dc_c30_0041)

lemma dc_c30_0042: "dc_sub dc_b30 42"
  by (dc_eval dc_c30_0042)

lemma dc_c30_0043: "dc_sub dc_b30 43"
  by (dc_eval dc_c30_0043)

lemma dc_c30_0044: "dc_sub dc_b30 44"
  by (dc_eval dc_c30_0044)

lemma dc_c30_0045: "dc_sub dc_b30 45"
  by (dc_eval dc_c30_0045)

lemma dc_c30_0046: "dc_sub dc_b30 46"
  by (dc_eval dc_c30_0046)

lemma dc_c30_0047: "dc_sub dc_b30 47"
  by (dc_eval dc_c30_0047)

lemma upt_c30_002: "[32..<48] = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]"
  by (simp add: upt_rec)

lemma sec_c30_002: "\<forall>j\<in>{16 * 2..<16 * 2 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 2..<16 * 2 + 16}"
  then have "j \<in> set [32..<48]" unfolding set_upt by simp
  then have "j \<in> set [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]" unfolding upt_c30_002 .
  then show "dc_sub dc_b30 j" using dc_c30_0032 dc_c30_0033 dc_c30_0034 dc_c30_0035 dc_c30_0036 dc_c30_0037 dc_c30_0038 dc_c30_0039 dc_c30_0040 dc_c30_0041 dc_c30_0042 dc_c30_0043 dc_c30_0044 dc_c30_0045 dc_c30_0046 dc_c30_0047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
