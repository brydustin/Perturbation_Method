theory OCX_nc_199
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3184: "oc_sub None 3184"
  by (oc_eval oc_nc_3184)

lemma oc_nc_3185: "oc_sub None 3185"
  by (oc_eval oc_nc_3185)

lemma oc_nc_3186: "oc_sub None 3186"
  by (oc_eval oc_nc_3186)

lemma oc_nc_3187: "oc_sub None 3187"
  by (oc_eval oc_nc_3187)

lemma oc_nc_3188: "oc_sub None 3188"
  by (oc_eval oc_nc_3188)

lemma oc_nc_3189: "oc_sub None 3189"
  by (oc_eval oc_nc_3189)

lemma oc_nc_3190: "oc_sub None 3190"
  by (oc_eval oc_nc_3190)

lemma oc_nc_3191: "oc_sub None 3191"
  by (oc_eval oc_nc_3191)

lemma oc_nc_3192: "oc_sub None 3192"
  by (oc_eval oc_nc_3192)

lemma oc_nc_3193: "oc_sub None 3193"
  by (oc_eval oc_nc_3193)

lemma oc_nc_3194: "oc_sub None 3194"
  by (oc_eval oc_nc_3194)

lemma oc_nc_3195: "oc_sub None 3195"
  by (oc_eval oc_nc_3195)

lemma oc_nc_3196: "oc_sub None 3196"
  by (oc_eval oc_nc_3196)

lemma oc_nc_3197: "oc_sub None 3197"
  by (oc_eval oc_nc_3197)

lemma oc_nc_3198: "oc_sub None 3198"
  by (oc_eval oc_nc_3198)

lemma oc_nc_3199: "oc_sub None 3199"
  by (oc_eval oc_nc_3199)

lemma upt_nc_199: "[3184..<3200] = [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]"
  by (simp add: upt_rec)

lemma sec_nc_199: "\<forall>j\<in>{16 * 199..<16 * 199 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 199..<16 * 199 + 16}"
  then have "j \<in> set [3184..<3200]" unfolding set_upt by simp
  then have "j \<in> set [3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199]" unfolding upt_nc_199 .
  then show "oc_sub None j" using oc_nc_3184 oc_nc_3185 oc_nc_3186 oc_nc_3187 oc_nc_3188 oc_nc_3189 oc_nc_3190 oc_nc_3191 oc_nc_3192 oc_nc_3193 oc_nc_3194 oc_nc_3195 oc_nc_3196 oc_nc_3197 oc_nc_3198 oc_nc_3199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
