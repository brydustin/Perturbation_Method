theory OCX_c30_002
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0032: "oc_sub oc_b30 32"
  by (oc_eval oc_c30_0032)

lemma oc_c30_0033: "oc_sub oc_b30 33"
  by (oc_eval oc_c30_0033)

lemma oc_c30_0034: "oc_sub oc_b30 34"
  by (oc_eval oc_c30_0034)

lemma oc_c30_0035: "oc_sub oc_b30 35"
  by (oc_eval oc_c30_0035)

lemma oc_c30_0036: "oc_sub oc_b30 36"
  by (oc_eval oc_c30_0036)

lemma oc_c30_0037: "oc_sub oc_b30 37"
  by (oc_eval oc_c30_0037)

lemma oc_c30_0038: "oc_sub oc_b30 38"
  by (oc_eval oc_c30_0038)

lemma oc_c30_0039: "oc_sub oc_b30 39"
  by (oc_eval oc_c30_0039)

lemma oc_c30_0040: "oc_sub oc_b30 40"
  by (oc_eval oc_c30_0040)

lemma oc_c30_0041: "oc_sub oc_b30 41"
  by (oc_eval oc_c30_0041)

lemma oc_c30_0042: "oc_sub oc_b30 42"
  by (oc_eval oc_c30_0042)

lemma oc_c30_0043: "oc_sub oc_b30 43"
  by (oc_eval oc_c30_0043)

lemma oc_c30_0044: "oc_sub oc_b30 44"
  by (oc_eval oc_c30_0044)

lemma oc_c30_0045: "oc_sub oc_b30 45"
  by (oc_eval oc_c30_0045)

lemma oc_c30_0046: "oc_sub oc_b30 46"
  by (oc_eval oc_c30_0046)

lemma oc_c30_0047: "oc_sub oc_b30 47"
  by (oc_eval oc_c30_0047)

lemma upt_c30_002: "[32..<48] = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]"
  by (simp add: upt_rec)

lemma sec_c30_002: "\<forall>j\<in>{16 * 2..<16 * 2 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 2..<16 * 2 + 16}"
  then have "j \<in> set [32..<48]" unfolding set_upt by simp
  then have "j \<in> set [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]" unfolding upt_c30_002 .
  then show "oc_sub oc_b30 j" using oc_c30_0032 oc_c30_0033 oc_c30_0034 oc_c30_0035 oc_c30_0036 oc_c30_0037 oc_c30_0038 oc_c30_0039 oc_c30_0040 oc_c30_0041 oc_c30_0042 oc_c30_0043 oc_c30_0044 oc_c30_0045 oc_c30_0046 oc_c30_0047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
