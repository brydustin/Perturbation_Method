theory OCX_c30_022
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0352: "oc_sub oc_b30 352"
  by (oc_eval oc_c30_0352)

lemma oc_c30_0353: "oc_sub oc_b30 353"
  by (oc_eval oc_c30_0353)

lemma oc_c30_0354: "oc_sub oc_b30 354"
  by (oc_eval oc_c30_0354)

lemma oc_c30_0355: "oc_sub oc_b30 355"
  by (oc_eval oc_c30_0355)

lemma oc_c30_0356: "oc_sub oc_b30 356"
  by (oc_eval oc_c30_0356)

lemma oc_c30_0357: "oc_sub oc_b30 357"
  by (oc_eval oc_c30_0357)

lemma oc_c30_0358: "oc_sub oc_b30 358"
  by (oc_eval oc_c30_0358)

lemma oc_c30_0359: "oc_sub oc_b30 359"
  by (oc_eval oc_c30_0359)

lemma oc_c30_0360: "oc_sub oc_b30 360"
  by (oc_eval oc_c30_0360)

lemma oc_c30_0361: "oc_sub oc_b30 361"
  by (oc_eval oc_c30_0361)

lemma oc_c30_0362: "oc_sub oc_b30 362"
  by (oc_eval oc_c30_0362)

lemma oc_c30_0363: "oc_sub oc_b30 363"
  by (oc_eval oc_c30_0363)

lemma oc_c30_0364: "oc_sub oc_b30 364"
  by (oc_eval oc_c30_0364)

lemma oc_c30_0365: "oc_sub oc_b30 365"
  by (oc_eval oc_c30_0365)

lemma oc_c30_0366: "oc_sub oc_b30 366"
  by (oc_eval oc_c30_0366)

lemma oc_c30_0367: "oc_sub oc_b30 367"
  by (oc_eval oc_c30_0367)

lemma upt_c30_022: "[352..<368] = [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]"
  by (simp add: upt_rec)

lemma sec_c30_022: "\<forall>j\<in>{16 * 22..<16 * 22 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 22..<16 * 22 + 16}"
  then have "j \<in> set [352..<368]" unfolding set_upt by simp
  then have "j \<in> set [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]" unfolding upt_c30_022 .
  then show "oc_sub oc_b30 j" using oc_c30_0352 oc_c30_0353 oc_c30_0354 oc_c30_0355 oc_c30_0356 oc_c30_0357 oc_c30_0358 oc_c30_0359 oc_c30_0360 oc_c30_0361 oc_c30_0362 oc_c30_0363 oc_c30_0364 oc_c30_0365 oc_c30_0366 oc_c30_0367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
