theory DCX_nc_022
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0352: "dc_sub None 352"
  by (dc_eval dc_nc_0352)

lemma dc_nc_0353: "dc_sub None 353"
  by (dc_eval dc_nc_0353)

lemma dc_nc_0354: "dc_sub None 354"
  by (dc_eval dc_nc_0354)

lemma dc_nc_0355: "dc_sub None 355"
  by (dc_eval dc_nc_0355)

lemma dc_nc_0356: "dc_sub None 356"
  by (dc_eval dc_nc_0356)

lemma dc_nc_0357: "dc_sub None 357"
  by (dc_eval dc_nc_0357)

lemma dc_nc_0358: "dc_sub None 358"
  by (dc_eval dc_nc_0358)

lemma dc_nc_0359: "dc_sub None 359"
  by (dc_eval dc_nc_0359)

lemma dc_nc_0360: "dc_sub None 360"
  by (dc_eval dc_nc_0360)

lemma dc_nc_0361: "dc_sub None 361"
  by (dc_eval dc_nc_0361)

lemma dc_nc_0362: "dc_sub None 362"
  by (dc_eval dc_nc_0362)

lemma dc_nc_0363: "dc_sub None 363"
  by (dc_eval dc_nc_0363)

lemma dc_nc_0364: "dc_sub None 364"
  by (dc_eval dc_nc_0364)

lemma dc_nc_0365: "dc_sub None 365"
  by (dc_eval dc_nc_0365)

lemma dc_nc_0366: "dc_sub None 366"
  by (dc_eval dc_nc_0366)

lemma dc_nc_0367: "dc_sub None 367"
  by (dc_eval dc_nc_0367)

lemma upt_nc_022: "[352..<368] = [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]"
  by (simp add: upt_rec)

lemma sec_nc_022: "\<forall>j\<in>{16 * 22..<16 * 22 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 22..<16 * 22 + 16}"
  then have "j \<in> set [352..<368]" unfolding set_upt by simp
  then have "j \<in> set [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]" unfolding upt_nc_022 .
  then show "dc_sub None j" using dc_nc_0352 dc_nc_0353 dc_nc_0354 dc_nc_0355 dc_nc_0356 dc_nc_0357 dc_nc_0358 dc_nc_0359 dc_nc_0360 dc_nc_0361 dc_nc_0362 dc_nc_0363 dc_nc_0364 dc_nc_0365 dc_nc_0366 dc_nc_0367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
