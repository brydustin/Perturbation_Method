theory DCX_nc_005
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0080: "dc_sub None 80"
  by (dc_eval dc_nc_0080)

lemma dc_nc_0081: "dc_sub None 81"
  by (dc_eval dc_nc_0081)

lemma dc_nc_0082: "dc_sub None 82"
  by (dc_eval dc_nc_0082)

lemma dc_nc_0083: "dc_sub None 83"
  by (dc_eval dc_nc_0083)

lemma dc_nc_0084: "dc_sub None 84"
  by (dc_eval dc_nc_0084)

lemma dc_nc_0085: "dc_sub None 85"
  by (dc_eval dc_nc_0085)

lemma dc_nc_0086: "dc_sub None 86"
  by (dc_eval dc_nc_0086)

lemma dc_nc_0087: "dc_sub None 87"
  by (dc_eval dc_nc_0087)

lemma dc_nc_0088: "dc_sub None 88"
  by (dc_eval dc_nc_0088)

lemma dc_nc_0089: "dc_sub None 89"
  by (dc_eval dc_nc_0089)

lemma dc_nc_0090: "dc_sub None 90"
  by (dc_eval dc_nc_0090)

lemma dc_nc_0091: "dc_sub None 91"
  by (dc_eval dc_nc_0091)

lemma dc_nc_0092: "dc_sub None 92"
  by (dc_eval dc_nc_0092)

lemma dc_nc_0093: "dc_sub None 93"
  by (dc_eval dc_nc_0093)

lemma dc_nc_0094: "dc_sub None 94"
  by (dc_eval dc_nc_0094)

lemma dc_nc_0095: "dc_sub None 95"
  by (dc_eval dc_nc_0095)

lemma upt_nc_005: "[80..<96] = [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]"
  by (simp add: upt_rec)

lemma sec_nc_005: "\<forall>j\<in>{16 * 5..<16 * 5 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 5..<16 * 5 + 16}"
  then have "j \<in> set [80..<96]" unfolding set_upt by simp
  then have "j \<in> set [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]" unfolding upt_nc_005 .
  then show "dc_sub None j" using dc_nc_0080 dc_nc_0081 dc_nc_0082 dc_nc_0083 dc_nc_0084 dc_nc_0085 dc_nc_0086 dc_nc_0087 dc_nc_0088 dc_nc_0089 dc_nc_0090 dc_nc_0091 dc_nc_0092 dc_nc_0093 dc_nc_0094 dc_nc_0095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
