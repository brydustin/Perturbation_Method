theory GDCX_nc_022
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0352: "gdc_sub None 352"
  by (gdc_eval gdc_nc_0352)

lemma gdc_nc_0353: "gdc_sub None 353"
  by (gdc_eval gdc_nc_0353)

lemma gdc_nc_0354: "gdc_sub None 354"
  by (gdc_eval gdc_nc_0354)

lemma gdc_nc_0355: "gdc_sub None 355"
  by (gdc_eval gdc_nc_0355)

lemma gdc_nc_0356: "gdc_sub None 356"
  by (gdc_eval gdc_nc_0356)

lemma gdc_nc_0357: "gdc_sub None 357"
  by (gdc_eval gdc_nc_0357)

lemma gdc_nc_0358: "gdc_sub None 358"
  by (gdc_eval gdc_nc_0358)

lemma gdc_nc_0359: "gdc_sub None 359"
  by (gdc_eval gdc_nc_0359)

lemma gdc_nc_0360: "gdc_sub None 360"
  by (gdc_eval gdc_nc_0360)

lemma gdc_nc_0361: "gdc_sub None 361"
  by (gdc_eval gdc_nc_0361)

lemma gdc_nc_0362: "gdc_sub None 362"
  by (gdc_eval gdc_nc_0362)

lemma gdc_nc_0363: "gdc_sub None 363"
  by (gdc_eval gdc_nc_0363)

lemma gdc_nc_0364: "gdc_sub None 364"
  by (gdc_eval gdc_nc_0364)

lemma gdc_nc_0365: "gdc_sub None 365"
  by (gdc_eval gdc_nc_0365)

lemma gdc_nc_0366: "gdc_sub None 366"
  by (gdc_eval gdc_nc_0366)

lemma gdc_nc_0367: "gdc_sub None 367"
  by (gdc_eval gdc_nc_0367)

lemma gupt_nc_022: "[352..<368] = [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]"
  by (simp add: upt_rec)

lemma gsec_nc_022: "\<forall>j\<in>{16 * 22..<16 * 22 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 22..<16 * 22 + 16}"
  then have "j \<in> set [352..<368]" unfolding set_upt by simp
  then have "j \<in> set [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]" unfolding gupt_nc_022 .
  then show "gdc_sub None j" using gdc_nc_0352 gdc_nc_0353 gdc_nc_0354 gdc_nc_0355 gdc_nc_0356 gdc_nc_0357 gdc_nc_0358 gdc_nc_0359 gdc_nc_0360 gdc_nc_0361 gdc_nc_0362 gdc_nc_0363 gdc_nc_0364 gdc_nc_0365 gdc_nc_0366 gdc_nc_0367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
