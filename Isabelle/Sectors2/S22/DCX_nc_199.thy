theory DCX_nc_199
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3184: "dc_sub None 3184"
  by (dc_eval dc_nc_3184)

lemma dc_nc_3185: "dc_sub None 3185"
  by (dc_eval dc_nc_3185)

lemma dc_nc_3186: "dc_sub None 3186"
  by (dc_eval dc_nc_3186)

lemma dc_nc_3187: "dc_sub None 3187"
  by (dc_eval dc_nc_3187)

lemma dc_nc_3188: "dc_sub None 3188"
  by (dc_eval dc_nc_3188)

lemma dc_nc_3189: "dc_sub None 3189"
  by (dc_eval dc_nc_3189)

lemma dc_nc_3190: "dc_sub None 3190"
  by (dc_eval dc_nc_3190)

lemma dc_nc_3191: "dc_sub None 3191"
  by (dc_eval dc_nc_3191)

lemma dc_nc_3192: "dc_sub None 3192"
  by (dc_eval dc_nc_3192)

lemma dc_nc_3193: "dc_sub None 3193"
  by (dc_eval dc_nc_3193)

lemma dc_nc_3194: "dc_sub None 3194"
  by (dc_eval dc_nc_3194)

lemma dc_nc_3195: "dc_sub None 3195"
  by (dc_eval dc_nc_3195)

lemma dc_nc_3196: "dc_sub None 3196"
  by (dc_eval dc_nc_3196)

lemma dc_nc_3197: "dc_sub None 3197"
  by (dc_eval dc_nc_3197)

lemma dc_nc_3198: "dc_sub None 3198"
  by (dc_eval dc_nc_3198)

lemma dc_nc_3199: "dc_sub None 3199"
  by (dc_eval dc_nc_3199)

lemma upt_nc_199: "[3184..<3200] = [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]"
  by (simp add: upt_rec)

lemma sec_nc_199: "\<forall>j\<in>{16 * 199..<16 * 199 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 199..<16 * 199 + 16}"
  then have "j \<in> set [3184..<3200]" unfolding set_upt by simp
  then have "j \<in> set [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]" unfolding upt_nc_199 .
  then show "dc_sub None j" using dc_nc_3184 dc_nc_3185 dc_nc_3186 dc_nc_3187 dc_nc_3188 dc_nc_3189 dc_nc_3190 dc_nc_3191 dc_nc_3192 dc_nc_3193 dc_nc_3194 dc_nc_3195 dc_nc_3196 dc_nc_3197 dc_nc_3198 dc_nc_3199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
