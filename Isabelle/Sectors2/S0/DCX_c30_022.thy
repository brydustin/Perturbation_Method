theory DCX_c30_022
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0352: "dc_sub dc_b30 352"
  by (dc_eval dc_c30_0352)

lemma dc_c30_0353: "dc_sub dc_b30 353"
  by (dc_eval dc_c30_0353)

lemma dc_c30_0354: "dc_sub dc_b30 354"
  by (dc_eval dc_c30_0354)

lemma dc_c30_0355: "dc_sub dc_b30 355"
  by (dc_eval dc_c30_0355)

lemma dc_c30_0356: "dc_sub dc_b30 356"
  by (dc_eval dc_c30_0356)

lemma dc_c30_0357: "dc_sub dc_b30 357"
  by (dc_eval dc_c30_0357)

lemma dc_c30_0358: "dc_sub dc_b30 358"
  by (dc_eval dc_c30_0358)

lemma dc_c30_0359: "dc_sub dc_b30 359"
  by (dc_eval dc_c30_0359)

lemma dc_c30_0360: "dc_sub dc_b30 360"
  by (dc_eval dc_c30_0360)

lemma dc_c30_0361: "dc_sub dc_b30 361"
  by (dc_eval dc_c30_0361)

lemma dc_c30_0362: "dc_sub dc_b30 362"
  by (dc_eval dc_c30_0362)

lemma dc_c30_0363: "dc_sub dc_b30 363"
  by (dc_eval dc_c30_0363)

lemma dc_c30_0364: "dc_sub dc_b30 364"
  by (dc_eval dc_c30_0364)

lemma dc_c30_0365: "dc_sub dc_b30 365"
  by (dc_eval dc_c30_0365)

lemma dc_c30_0366: "dc_sub dc_b30 366"
  by (dc_eval dc_c30_0366)

lemma dc_c30_0367: "dc_sub dc_b30 367"
  by (dc_eval dc_c30_0367)

lemma upt_c30_022: "[352..<368] = [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]"
  by (simp add: upt_rec)

lemma sec_c30_022: "\<forall>j\<in>{16 * 22..<16 * 22 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 22..<16 * 22 + 16}"
  then have "j \<in> set [352..<368]" unfolding set_upt by simp
  then have "j \<in> set [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]" unfolding upt_c30_022 .
  then show "dc_sub dc_b30 j" using dc_c30_0352 dc_c30_0353 dc_c30_0354 dc_c30_0355 dc_c30_0356 dc_c30_0357 dc_c30_0358 dc_c30_0359 dc_c30_0360 dc_c30_0361 dc_c30_0362 dc_c30_0363 dc_c30_0364 dc_c30_0365 dc_c30_0366 dc_c30_0367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
