theory GDCX_nc_199
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3184: "gdc_sub None 3184"
  by (gdc_eval gdc_nc_3184)

lemma gdc_nc_3185: "gdc_sub None 3185"
  by (gdc_eval gdc_nc_3185)

lemma gdc_nc_3186: "gdc_sub None 3186"
  by (gdc_eval gdc_nc_3186)

lemma gdc_nc_3187: "gdc_sub None 3187"
  by (gdc_eval gdc_nc_3187)

lemma gdc_nc_3188: "gdc_sub None 3188"
  by (gdc_eval gdc_nc_3188)

lemma gdc_nc_3189: "gdc_sub None 3189"
  by (gdc_eval gdc_nc_3189)

lemma gdc_nc_3190: "gdc_sub None 3190"
  by (gdc_eval gdc_nc_3190)

lemma gdc_nc_3191: "gdc_sub None 3191"
  by (gdc_eval gdc_nc_3191)

lemma gdc_nc_3192: "gdc_sub None 3192"
  by (gdc_eval gdc_nc_3192)

lemma gdc_nc_3193: "gdc_sub None 3193"
  by (gdc_eval gdc_nc_3193)

lemma gdc_nc_3194: "gdc_sub None 3194"
  by (gdc_eval gdc_nc_3194)

lemma gdc_nc_3195: "gdc_sub None 3195"
  by (gdc_eval gdc_nc_3195)

lemma gdc_nc_3196: "gdc_sub None 3196"
  by (gdc_eval gdc_nc_3196)

lemma gdc_nc_3197: "gdc_sub None 3197"
  by (gdc_eval gdc_nc_3197)

lemma gdc_nc_3198: "gdc_sub None 3198"
  by (gdc_eval gdc_nc_3198)

lemma gdc_nc_3199: "gdc_sub None 3199"
  by (gdc_eval gdc_nc_3199)

lemma gupt_nc_199: "[3184..<3200] = [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]"
  by (simp add: upt_rec)

lemma gsec_nc_199: "\<forall>j\<in>{16 * 199..<16 * 199 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 199..<16 * 199 + 16}"
  then have "j \<in> set [3184..<3200]" unfolding set_upt by simp
  then have "j \<in> set [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]" unfolding gupt_nc_199 .
  then show "gdc_sub None j" using gdc_nc_3184 gdc_nc_3185 gdc_nc_3186 gdc_nc_3187 gdc_nc_3188 gdc_nc_3189 gdc_nc_3190 gdc_nc_3191 gdc_nc_3192 gdc_nc_3193 gdc_nc_3194 gdc_nc_3195 gdc_nc_3196 gdc_nc_3197 gdc_nc_3198 gdc_nc_3199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
