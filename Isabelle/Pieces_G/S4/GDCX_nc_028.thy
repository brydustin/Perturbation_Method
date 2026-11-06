theory GDCX_nc_028
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0448: "gdc_sub None 448"
  by (gdc_eval gdc_nc_0448)

lemma gdc_nc_0449: "gdc_sub None 449"
  by (gdc_eval gdc_nc_0449)

lemma gdc_nc_0450: "gdc_sub None 450"
  by (gdc_eval gdc_nc_0450)

lemma gdc_nc_0451: "gdc_sub None 451"
  by (gdc_eval gdc_nc_0451)

lemma gdc_nc_0452: "gdc_sub None 452"
  by (gdc_eval gdc_nc_0452)

lemma gdc_nc_0453: "gdc_sub None 453"
  by (gdc_eval gdc_nc_0453)

lemma gdc_nc_0454: "gdc_sub None 454"
  by (gdc_eval gdc_nc_0454)

lemma gdc_nc_0455: "gdc_sub None 455"
  by (gdc_eval gdc_nc_0455)

lemma gdc_nc_0456: "gdc_sub None 456"
  by (gdc_eval gdc_nc_0456)

lemma gdc_nc_0457: "gdc_sub None 457"
  by (gdc_eval gdc_nc_0457)

lemma gdc_nc_0458: "gdc_sub None 458"
  by (gdc_eval gdc_nc_0458)

lemma gdc_nc_0459: "gdc_sub None 459"
  by (gdc_eval gdc_nc_0459)

lemma gdc_nc_0460: "gdc_sub None 460"
  by (gdc_eval gdc_nc_0460)

lemma gdc_nc_0461: "gdc_sub None 461"
  by (gdc_eval gdc_nc_0461)

lemma gdc_nc_0462: "gdc_sub None 462"
  by (gdc_eval gdc_nc_0462)

lemma gdc_nc_0463: "gdc_sub None 463"
  by (gdc_eval gdc_nc_0463)

lemma gupt_nc_028: "[448..<464] = [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]"
  by (simp add: upt_rec)

lemma gsec_nc_028: "\<forall>j\<in>{16 * 28..<16 * 28 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 28..<16 * 28 + 16}"
  then have "j \<in> set [448..<464]" unfolding set_upt by simp
  then have "j \<in> set [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]" unfolding gupt_nc_028 .
  then show "gdc_sub None j" using gdc_nc_0448 gdc_nc_0449 gdc_nc_0450 gdc_nc_0451 gdc_nc_0452 gdc_nc_0453 gdc_nc_0454 gdc_nc_0455 gdc_nc_0456 gdc_nc_0457 gdc_nc_0458 gdc_nc_0459 gdc_nc_0460 gdc_nc_0461 gdc_nc_0462 gdc_nc_0463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
