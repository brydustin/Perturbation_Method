theory DCX_c30_199
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3184: "dc_sub dc_b30 3184"
  by (dc_eval dc_c30_3184)

lemma dc_c30_3185: "dc_sub dc_b30 3185"
  by (dc_eval dc_c30_3185)

lemma dc_c30_3186: "dc_sub dc_b30 3186"
  by (dc_eval dc_c30_3186)

lemma dc_c30_3187: "dc_sub dc_b30 3187"
  by (dc_eval dc_c30_3187)

lemma dc_c30_3188: "dc_sub dc_b30 3188"
  by (dc_eval dc_c30_3188)

lemma dc_c30_3189: "dc_sub dc_b30 3189"
  by (dc_eval dc_c30_3189)

lemma dc_c30_3190: "dc_sub dc_b30 3190"
  by (dc_eval dc_c30_3190)

lemma dc_c30_3191: "dc_sub dc_b30 3191"
  by (dc_eval dc_c30_3191)

lemma dc_c30_3192: "dc_sub dc_b30 3192"
  by (dc_eval dc_c30_3192)

lemma dc_c30_3193: "dc_sub dc_b30 3193"
  by (dc_eval dc_c30_3193)

lemma dc_c30_3194: "dc_sub dc_b30 3194"
  by (dc_eval dc_c30_3194)

lemma dc_c30_3195: "dc_sub dc_b30 3195"
  by (dc_eval dc_c30_3195)

lemma dc_c30_3196: "dc_sub dc_b30 3196"
  by (dc_eval dc_c30_3196)

lemma dc_c30_3197: "dc_sub dc_b30 3197"
  by (dc_eval dc_c30_3197)

lemma dc_c30_3198: "dc_sub dc_b30 3198"
  by (dc_eval dc_c30_3198)

lemma dc_c30_3199: "dc_sub dc_b30 3199"
  by (dc_eval dc_c30_3199)

lemma upt_c30_199: "[3184..<3200] = [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]"
  by (simp add: upt_rec)

lemma sec_c30_199: "\<forall>j\<in>{16 * 199..<16 * 199 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 199..<16 * 199 + 16}"
  then have "j \<in> set [3184..<3200]" unfolding set_upt by simp
  then have "j \<in> set [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]" unfolding upt_c30_199 .
  then show "dc_sub dc_b30 j" using dc_c30_3184 dc_c30_3185 dc_c30_3186 dc_c30_3187 dc_c30_3188 dc_c30_3189 dc_c30_3190 dc_c30_3191 dc_c30_3192 dc_c30_3193 dc_c30_3194 dc_c30_3195 dc_c30_3196 dc_c30_3197 dc_c30_3198 dc_c30_3199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
