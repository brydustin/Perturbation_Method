theory OCX_nc_028
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0448: "oc_sub None 448"
  by (oc_eval oc_nc_0448)

lemma oc_nc_0449: "oc_sub None 449"
  by (oc_eval oc_nc_0449)

lemma oc_nc_0450: "oc_sub None 450"
  by (oc_eval oc_nc_0450)

lemma oc_nc_0451: "oc_sub None 451"
  by (oc_eval oc_nc_0451)

lemma oc_nc_0452: "oc_sub None 452"
  by (oc_eval oc_nc_0452)

lemma oc_nc_0453: "oc_sub None 453"
  by (oc_eval oc_nc_0453)

lemma oc_nc_0454: "oc_sub None 454"
  by (oc_eval oc_nc_0454)

lemma oc_nc_0455: "oc_sub None 455"
  by (oc_eval oc_nc_0455)

lemma oc_nc_0456: "oc_sub None 456"
  by (oc_eval oc_nc_0456)

lemma oc_nc_0457: "oc_sub None 457"
  by (oc_eval oc_nc_0457)

lemma oc_nc_0458: "oc_sub None 458"
  by (oc_eval oc_nc_0458)

lemma oc_nc_0459: "oc_sub None 459"
  by (oc_eval oc_nc_0459)

lemma oc_nc_0460: "oc_sub None 460"
  by (oc_eval oc_nc_0460)

lemma oc_nc_0461: "oc_sub None 461"
  by (oc_eval oc_nc_0461)

lemma oc_nc_0462: "oc_sub None 462"
  by (oc_eval oc_nc_0462)

lemma oc_nc_0463: "oc_sub None 463"
  by (oc_eval oc_nc_0463)

lemma upt_nc_028: "[448..<464] = [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]"
  by (simp add: upt_rec)

lemma sec_nc_028: "\<forall>j\<in>{16 * 28..<16 * 28 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 28..<16 * 28 + 16}"
  then have "j \<in> set [448..<464]" unfolding set_upt by simp
  then have "j \<in> set [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]" unfolding upt_nc_028 .
  then show "oc_sub None j" using oc_nc_0448 oc_nc_0449 oc_nc_0450 oc_nc_0451 oc_nc_0452 oc_nc_0453 oc_nc_0454 oc_nc_0455 oc_nc_0456 oc_nc_0457 oc_nc_0458 oc_nc_0459 oc_nc_0460 oc_nc_0461 oc_nc_0462 oc_nc_0463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
