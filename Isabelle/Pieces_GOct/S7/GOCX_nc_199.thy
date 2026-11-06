theory GOCX_nc_199
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3184: "goc_sub None 3184"
  by (goc_eval goc_nc_3184)

lemma goc_nc_3185: "goc_sub None 3185"
  by (goc_eval goc_nc_3185)

lemma goc_nc_3186: "goc_sub None 3186"
  by (goc_eval goc_nc_3186)

lemma goc_nc_3187: "goc_sub None 3187"
  by (goc_eval goc_nc_3187)

lemma goc_nc_3188: "goc_sub None 3188"
  by (goc_eval goc_nc_3188)

lemma goc_nc_3189: "goc_sub None 3189"
  by (goc_eval goc_nc_3189)

lemma goc_nc_3190: "goc_sub None 3190"
  by (goc_eval goc_nc_3190)

lemma goc_nc_3191: "goc_sub None 3191"
  by (goc_eval goc_nc_3191)

lemma goc_nc_3192: "goc_sub None 3192"
  by (goc_eval goc_nc_3192)

lemma goc_nc_3193: "goc_sub None 3193"
  by (goc_eval goc_nc_3193)

lemma goc_nc_3194: "goc_sub None 3194"
  by (goc_eval goc_nc_3194)

lemma goc_nc_3195: "goc_sub None 3195"
  by (goc_eval goc_nc_3195)

lemma goc_nc_3196: "goc_sub None 3196"
  by (goc_eval goc_nc_3196)

lemma goc_nc_3197: "goc_sub None 3197"
  by (goc_eval goc_nc_3197)

lemma goc_nc_3198: "goc_sub None 3198"
  by (goc_eval goc_nc_3198)

lemma goc_nc_3199: "goc_sub None 3199"
  by (goc_eval goc_nc_3199)

lemma gupt_nc_199: "[3184..<3200] = [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]"
  by (simp add: upt_rec)

lemma gsec_nc_199: "\<forall>j\<in>{16 * 199..<16 * 199 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 199..<16 * 199 + 16}"
  then have "j \<in> set [3184..<3200]" unfolding set_upt by simp
  then have "j \<in> set [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]" unfolding gupt_nc_199 .
  then show "goc_sub None j" using goc_nc_3184 goc_nc_3185 goc_nc_3186 goc_nc_3187 goc_nc_3188 goc_nc_3189 goc_nc_3190 goc_nc_3191 goc_nc_3192 goc_nc_3193 goc_nc_3194 goc_nc_3195 goc_nc_3196 goc_nc_3197 goc_nc_3198 goc_nc_3199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
