theory OCX_nc_022
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0352: "oc_sub None 352"
  by (oc_eval oc_nc_0352)

lemma oc_nc_0353: "oc_sub None 353"
  by (oc_eval oc_nc_0353)

lemma oc_nc_0354: "oc_sub None 354"
  by (oc_eval oc_nc_0354)

lemma oc_nc_0355: "oc_sub None 355"
  by (oc_eval oc_nc_0355)

lemma oc_nc_0356: "oc_sub None 356"
  by (oc_eval oc_nc_0356)

lemma oc_nc_0357: "oc_sub None 357"
  by (oc_eval oc_nc_0357)

lemma oc_nc_0358: "oc_sub None 358"
  by (oc_eval oc_nc_0358)

lemma oc_nc_0359: "oc_sub None 359"
  by (oc_eval oc_nc_0359)

lemma oc_nc_0360: "oc_sub None 360"
  by (oc_eval oc_nc_0360)

lemma oc_nc_0361: "oc_sub None 361"
  by (oc_eval oc_nc_0361)

lemma oc_nc_0362: "oc_sub None 362"
  by (oc_eval oc_nc_0362)

lemma oc_nc_0363: "oc_sub None 363"
  by (oc_eval oc_nc_0363)

lemma oc_nc_0364: "oc_sub None 364"
  by (oc_eval oc_nc_0364)

lemma oc_nc_0365: "oc_sub None 365"
  by (oc_eval oc_nc_0365)

lemma oc_nc_0366: "oc_sub None 366"
  by (oc_eval oc_nc_0366)

lemma oc_nc_0367: "oc_sub None 367"
  by (oc_eval oc_nc_0367)

lemma upt_nc_022: "[352..<368] = [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]"
  by (simp add: upt_rec)

lemma sec_nc_022: "\<forall>j\<in>{16 * 22..<16 * 22 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 22..<16 * 22 + 16}"
  then have "j \<in> set [352..<368]" unfolding set_upt by simp
  then have "j \<in> set [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]" unfolding upt_nc_022 .
  then show "oc_sub None j" using oc_nc_0352 oc_nc_0353 oc_nc_0354 oc_nc_0355 oc_nc_0356 oc_nc_0357 oc_nc_0358 oc_nc_0359 oc_nc_0360 oc_nc_0361 oc_nc_0362 oc_nc_0363 oc_nc_0364 oc_nc_0365 oc_nc_0366 oc_nc_0367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
