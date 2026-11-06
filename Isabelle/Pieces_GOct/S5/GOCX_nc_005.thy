theory GOCX_nc_005
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0080: "goc_sub None 80"
  by (goc_eval goc_nc_0080)

lemma goc_nc_0081: "goc_sub None 81"
  by (goc_eval goc_nc_0081)

lemma goc_nc_0082: "goc_sub None 82"
  by (goc_eval goc_nc_0082)

lemma goc_nc_0083: "goc_sub None 83"
  by (goc_eval goc_nc_0083)

lemma goc_nc_0084: "goc_sub None 84"
  by (goc_eval goc_nc_0084)

lemma goc_nc_0085: "goc_sub None 85"
  by (goc_eval goc_nc_0085)

lemma goc_nc_0086: "goc_sub None 86"
  by (goc_eval goc_nc_0086)

lemma goc_nc_0087: "goc_sub None 87"
  by (goc_eval goc_nc_0087)

lemma goc_nc_0088: "goc_sub None 88"
  by (goc_eval goc_nc_0088)

lemma goc_nc_0089: "goc_sub None 89"
  by (goc_eval goc_nc_0089)

lemma goc_nc_0090: "goc_sub None 90"
  by (goc_eval goc_nc_0090)

lemma goc_nc_0091: "goc_sub None 91"
  by (goc_eval goc_nc_0091)

lemma goc_nc_0092: "goc_sub None 92"
  by (goc_eval goc_nc_0092)

lemma goc_nc_0093: "goc_sub None 93"
  by (goc_eval goc_nc_0093)

lemma goc_nc_0094: "goc_sub None 94"
  by (goc_eval goc_nc_0094)

lemma goc_nc_0095: "goc_sub None 95"
  by (goc_eval goc_nc_0095)

lemma gupt_nc_005: "[80..<96] = [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]"
  by (simp add: upt_rec)

lemma gsec_nc_005: "\<forall>j\<in>{16 * 5..<16 * 5 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 5..<16 * 5 + 16}"
  then have "j \<in> set [80..<96]" unfolding set_upt by simp
  then have "j \<in> set [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]" unfolding gupt_nc_005 .
  then show "goc_sub None j" using goc_nc_0080 goc_nc_0081 goc_nc_0082 goc_nc_0083 goc_nc_0084 goc_nc_0085 goc_nc_0086 goc_nc_0087 goc_nc_0088 goc_nc_0089 goc_nc_0090 goc_nc_0091 goc_nc_0092 goc_nc_0093 goc_nc_0094 goc_nc_0095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
