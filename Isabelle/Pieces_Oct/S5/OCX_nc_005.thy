theory OCX_nc_005
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0080: "oc_sub None 80"
  by (oc_eval oc_nc_0080)

lemma oc_nc_0081: "oc_sub None 81"
  by (oc_eval oc_nc_0081)

lemma oc_nc_0082: "oc_sub None 82"
  by (oc_eval oc_nc_0082)

lemma oc_nc_0083: "oc_sub None 83"
  by (oc_eval oc_nc_0083)

lemma oc_nc_0084: "oc_sub None 84"
  by (oc_eval oc_nc_0084)

lemma oc_nc_0085: "oc_sub None 85"
  by (oc_eval oc_nc_0085)

lemma oc_nc_0086: "oc_sub None 86"
  by (oc_eval oc_nc_0086)

lemma oc_nc_0087: "oc_sub None 87"
  by (oc_eval oc_nc_0087)

lemma oc_nc_0088: "oc_sub None 88"
  by (oc_eval oc_nc_0088)

lemma oc_nc_0089: "oc_sub None 89"
  by (oc_eval oc_nc_0089)

lemma oc_nc_0090: "oc_sub None 90"
  by (oc_eval oc_nc_0090)

lemma oc_nc_0091: "oc_sub None 91"
  by (oc_eval oc_nc_0091)

lemma oc_nc_0092: "oc_sub None 92"
  by (oc_eval oc_nc_0092)

lemma oc_nc_0093: "oc_sub None 93"
  by (oc_eval oc_nc_0093)

lemma oc_nc_0094: "oc_sub None 94"
  by (oc_eval oc_nc_0094)

lemma oc_nc_0095: "oc_sub None 95"
  by (oc_eval oc_nc_0095)

lemma upt_nc_005: "[80..<96] = [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]"
  by (simp add: upt_rec)

lemma sec_nc_005: "\<forall>j\<in>{16 * 5..<16 * 5 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 5..<16 * 5 + 16}"
  then have "j \<in> set [80..<96]" unfolding set_upt by simp
  then have "j \<in> set [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]" unfolding upt_nc_005 .
  then show "oc_sub None j" using oc_nc_0080 oc_nc_0081 oc_nc_0082 oc_nc_0083 oc_nc_0084 oc_nc_0085 oc_nc_0086 oc_nc_0087 oc_nc_0088 oc_nc_0089 oc_nc_0090 oc_nc_0091 oc_nc_0092 oc_nc_0093 oc_nc_0094 oc_nc_0095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
