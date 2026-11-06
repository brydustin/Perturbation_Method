theory GOCX_nc_022
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0352: "goc_sub None 352"
  by (goc_eval goc_nc_0352)

lemma goc_nc_0353: "goc_sub None 353"
  by (goc_eval goc_nc_0353)

lemma goc_nc_0354: "goc_sub None 354"
  by (goc_eval goc_nc_0354)

lemma goc_nc_0355: "goc_sub None 355"
  by (goc_eval goc_nc_0355)

lemma goc_nc_0356: "goc_sub None 356"
  by (goc_eval goc_nc_0356)

lemma goc_nc_0357: "goc_sub None 357"
  by (goc_eval goc_nc_0357)

lemma goc_nc_0358: "goc_sub None 358"
  by (goc_eval goc_nc_0358)

lemma goc_nc_0359: "goc_sub None 359"
  by (goc_eval goc_nc_0359)

lemma goc_nc_0360: "goc_sub None 360"
  by (goc_eval goc_nc_0360)

lemma goc_nc_0361: "goc_sub None 361"
  by (goc_eval goc_nc_0361)

lemma goc_nc_0362: "goc_sub None 362"
  by (goc_eval goc_nc_0362)

lemma goc_nc_0363: "goc_sub None 363"
  by (goc_eval goc_nc_0363)

lemma goc_nc_0364: "goc_sub None 364"
  by (goc_eval goc_nc_0364)

lemma goc_nc_0365: "goc_sub None 365"
  by (goc_eval goc_nc_0365)

lemma goc_nc_0366: "goc_sub None 366"
  by (goc_eval goc_nc_0366)

lemma goc_nc_0367: "goc_sub None 367"
  by (goc_eval goc_nc_0367)

lemma gupt_nc_022: "[352..<368] = [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]"
  by (simp add: upt_rec)

lemma gsec_nc_022: "\<forall>j\<in>{16 * 22..<16 * 22 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 22..<16 * 22 + 16}"
  then have "j \<in> set [352..<368]" unfolding set_upt by simp
  then have "j \<in> set [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]" unfolding gupt_nc_022 .
  then show "goc_sub None j" using goc_nc_0352 goc_nc_0353 goc_nc_0354 goc_nc_0355 goc_nc_0356 goc_nc_0357 goc_nc_0358 goc_nc_0359 goc_nc_0360 goc_nc_0361 goc_nc_0362 goc_nc_0363 goc_nc_0364 goc_nc_0365 goc_nc_0366 goc_nc_0367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
