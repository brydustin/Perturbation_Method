theory GDCX_nc_005
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0080: "gdc_sub None 80"
  by (gdc_eval gdc_nc_0080)

lemma gdc_nc_0081: "gdc_sub None 81"
  by (gdc_eval gdc_nc_0081)

lemma gdc_nc_0082: "gdc_sub None 82"
  by (gdc_eval gdc_nc_0082)

lemma gdc_nc_0083: "gdc_sub None 83"
  by (gdc_eval gdc_nc_0083)

lemma gdc_nc_0084: "gdc_sub None 84"
  by (gdc_eval gdc_nc_0084)

lemma gdc_nc_0085: "gdc_sub None 85"
  by (gdc_eval gdc_nc_0085)

lemma gdc_nc_0086: "gdc_sub None 86"
  by (gdc_eval gdc_nc_0086)

lemma gdc_nc_0087: "gdc_sub None 87"
  by (gdc_eval gdc_nc_0087)

lemma gdc_nc_0088: "gdc_sub None 88"
  by (gdc_eval gdc_nc_0088)

lemma gdc_nc_0089: "gdc_sub None 89"
  by (gdc_eval gdc_nc_0089)

lemma gdc_nc_0090: "gdc_sub None 90"
  by (gdc_eval gdc_nc_0090)

lemma gdc_nc_0091: "gdc_sub None 91"
  by (gdc_eval gdc_nc_0091)

lemma gdc_nc_0092: "gdc_sub None 92"
  by (gdc_eval gdc_nc_0092)

lemma gdc_nc_0093: "gdc_sub None 93"
  by (gdc_eval gdc_nc_0093)

lemma gdc_nc_0094: "gdc_sub None 94"
  by (gdc_eval gdc_nc_0094)

lemma gdc_nc_0095: "gdc_sub None 95"
  by (gdc_eval gdc_nc_0095)

lemma gupt_nc_005: "[80..<96] = [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]"
  by (simp add: upt_rec)

lemma gsec_nc_005: "\<forall>j\<in>{16 * 5..<16 * 5 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 5..<16 * 5 + 16}"
  then have "j \<in> set [80..<96]" unfolding set_upt by simp
  then have "j \<in> set [80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]" unfolding gupt_nc_005 .
  then show "gdc_sub None j" using gdc_nc_0080 gdc_nc_0081 gdc_nc_0082 gdc_nc_0083 gdc_nc_0084 gdc_nc_0085 gdc_nc_0086 gdc_nc_0087 gdc_nc_0088 gdc_nc_0089 gdc_nc_0090 gdc_nc_0091 gdc_nc_0092 gdc_nc_0093 gdc_nc_0094 gdc_nc_0095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
