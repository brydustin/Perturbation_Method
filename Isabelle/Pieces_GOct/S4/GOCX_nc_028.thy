theory GOCX_nc_028
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0448: "goc_sub None 448"
  by (goc_eval goc_nc_0448)

lemma goc_nc_0449: "goc_sub None 449"
  by (goc_eval goc_nc_0449)

lemma goc_nc_0450: "goc_sub None 450"
  by (goc_eval goc_nc_0450)

lemma goc_nc_0451: "goc_sub None 451"
  by (goc_eval goc_nc_0451)

lemma goc_nc_0452: "goc_sub None 452"
  by (goc_eval goc_nc_0452)

lemma goc_nc_0453: "goc_sub None 453"
  by (goc_eval goc_nc_0453)

lemma goc_nc_0454: "goc_sub None 454"
  by (goc_eval goc_nc_0454)

lemma goc_nc_0455: "goc_sub None 455"
  by (goc_eval goc_nc_0455)

lemma goc_nc_0456: "goc_sub None 456"
  by (goc_eval goc_nc_0456)

lemma goc_nc_0457: "goc_sub None 457"
  by (goc_eval goc_nc_0457)

lemma goc_nc_0458: "goc_sub None 458"
  by (goc_eval goc_nc_0458)

lemma goc_nc_0459: "goc_sub None 459"
  by (goc_eval goc_nc_0459)

lemma goc_nc_0460: "goc_sub None 460"
  by (goc_eval goc_nc_0460)

lemma goc_nc_0461: "goc_sub None 461"
  by (goc_eval goc_nc_0461)

lemma goc_nc_0462: "goc_sub None 462"
  by (goc_eval goc_nc_0462)

lemma goc_nc_0463: "goc_sub None 463"
  by (goc_eval goc_nc_0463)

lemma gupt_nc_028: "[448..<464] = [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]"
  by (simp add: upt_rec)

lemma gsec_nc_028: "\<forall>j\<in>{16 * 28..<16 * 28 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 28..<16 * 28 + 16}"
  then have "j \<in> set [448..<464]" unfolding set_upt by simp
  then have "j \<in> set [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]" unfolding gupt_nc_028 .
  then show "goc_sub None j" using goc_nc_0448 goc_nc_0449 goc_nc_0450 goc_nc_0451 goc_nc_0452 goc_nc_0453 goc_nc_0454 goc_nc_0455 goc_nc_0456 goc_nc_0457 goc_nc_0458 goc_nc_0459 goc_nc_0460 goc_nc_0461 goc_nc_0462 goc_nc_0463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
