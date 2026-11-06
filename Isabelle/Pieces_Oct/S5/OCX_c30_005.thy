theory OCX_c30_005
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0080: "oc_sub oc_b30 80"
  by (oc_eval oc_c30_0080)

lemma oc_c30_0081: "oc_sub oc_b30 81"
  by (oc_eval oc_c30_0081)

lemma oc_c30_0082: "oc_sub oc_b30 82"
  by (oc_eval oc_c30_0082)

lemma oc_c30_0083: "oc_sub oc_b30 83"
  by (oc_eval oc_c30_0083)

lemma oc_c30_0084: "oc_sub oc_b30 84"
  by (oc_eval oc_c30_0084)

lemma oc_c30_0085: "oc_sub oc_b30 85"
  by (oc_eval oc_c30_0085)

lemma oc_c30_0086: "oc_sub oc_b30 86"
  by (oc_eval oc_c30_0086)

lemma oc_c30_0087: "oc_sub oc_b30 87"
  by (oc_eval oc_c30_0087)

lemma oc_c30_0088: "oc_sub oc_b30 88"
  by (oc_eval oc_c30_0088)

lemma oc_c30_0089: "oc_sub oc_b30 89"
  by (oc_eval oc_c30_0089)

lemma oc_c30_0090: "oc_sub oc_b30 90"
  by (oc_eval oc_c30_0090)

lemma oc_c30_0091: "oc_sub oc_b30 91"
  by (oc_eval oc_c30_0091)

lemma oc_c30_0092: "oc_sub oc_b30 92"
  by (oc_eval oc_c30_0092)

lemma oc_c30_0093: "oc_sub oc_b30 93"
  by (oc_eval oc_c30_0093)

lemma oc_c30_0094: "oc_sub oc_b30 94"
  by (oc_eval oc_c30_0094)

lemma oc_c30_0095: "oc_sub oc_b30 95"
  by (oc_eval oc_c30_0095)

lemma upt_c30_005: "[80..<96] = [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]"
  by (simp add: upt_rec)

lemma sec_c30_005: "\<forall>j\<in>{16 * 5..<16 * 5 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 5..<16 * 5 + 16}"
  then have "j \<in> set [80..<96]" unfolding set_upt by simp
  then have "j \<in> set [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]" unfolding upt_c30_005 .
  then show "oc_sub oc_b30 j" using oc_c30_0080 oc_c30_0081 oc_c30_0082 oc_c30_0083 oc_c30_0084 oc_c30_0085 oc_c30_0086 oc_c30_0087 oc_c30_0088 oc_c30_0089 oc_c30_0090 oc_c30_0091 oc_c30_0092 oc_c30_0093 oc_c30_0094 oc_c30_0095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
