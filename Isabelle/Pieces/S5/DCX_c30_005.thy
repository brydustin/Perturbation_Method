theory DCX_c30_005
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0080: "dc_sub dc_b30 80"
  by (dc_eval dc_c30_0080)

lemma dc_c30_0081: "dc_sub dc_b30 81"
  by (dc_eval dc_c30_0081)

lemma dc_c30_0082: "dc_sub dc_b30 82"
  by (dc_eval dc_c30_0082)

lemma dc_c30_0083: "dc_sub dc_b30 83"
  by (dc_eval dc_c30_0083)

lemma dc_c30_0084: "dc_sub dc_b30 84"
  by (dc_eval dc_c30_0084)

lemma dc_c30_0085: "dc_sub dc_b30 85"
  by (dc_eval dc_c30_0085)

lemma dc_c30_0086: "dc_sub dc_b30 86"
  by (dc_eval dc_c30_0086)

lemma dc_c30_0087: "dc_sub dc_b30 87"
  by (dc_eval dc_c30_0087)

lemma dc_c30_0088: "dc_sub dc_b30 88"
  by (dc_eval dc_c30_0088)

lemma dc_c30_0089: "dc_sub dc_b30 89"
  by (dc_eval dc_c30_0089)

lemma dc_c30_0090: "dc_sub dc_b30 90"
  by (dc_eval dc_c30_0090)

lemma dc_c30_0091: "dc_sub dc_b30 91"
  by (dc_eval dc_c30_0091)

lemma dc_c30_0092: "dc_sub dc_b30 92"
  by (dc_eval dc_c30_0092)

lemma dc_c30_0093: "dc_sub dc_b30 93"
  by (dc_eval dc_c30_0093)

lemma dc_c30_0094: "dc_sub dc_b30 94"
  by (dc_eval dc_c30_0094)

lemma dc_c30_0095: "dc_sub dc_b30 95"
  by (dc_eval dc_c30_0095)

lemma upt_c30_005: "[80..<96] = [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]"
  by (simp add: upt_rec)

lemma sec_c30_005: "\<forall>j\<in>{16 * 5..<16 * 5 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 5..<16 * 5 + 16}"
  then have "j \<in> set [80..<96]" unfolding set_upt by simp
  then have "j \<in> set [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]" unfolding upt_c30_005 .
  then show "dc_sub dc_b30 j" using dc_c30_0080 dc_c30_0081 dc_c30_0082 dc_c30_0083 dc_c30_0084 dc_c30_0085 dc_c30_0086 dc_c30_0087 dc_c30_0088 dc_c30_0089 dc_c30_0090 dc_c30_0091 dc_c30_0092 dc_c30_0093 dc_c30_0094 dc_c30_0095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
