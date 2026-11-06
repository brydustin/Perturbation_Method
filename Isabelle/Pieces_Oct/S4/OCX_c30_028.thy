theory OCX_c30_028
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0448: "oc_sub oc_b30 448"
  by (oc_eval oc_c30_0448)

lemma oc_c30_0449: "oc_sub oc_b30 449"
  by (oc_eval oc_c30_0449)

lemma oc_c30_0450: "oc_sub oc_b30 450"
  by (oc_eval oc_c30_0450)

lemma oc_c30_0451: "oc_sub oc_b30 451"
  by (oc_eval oc_c30_0451)

lemma oc_c30_0452: "oc_sub oc_b30 452"
  by (oc_eval oc_c30_0452)

lemma oc_c30_0453: "oc_sub oc_b30 453"
  by (oc_eval oc_c30_0453)

lemma oc_c30_0454: "oc_sub oc_b30 454"
  by (oc_eval oc_c30_0454)

lemma oc_c30_0455: "oc_sub oc_b30 455"
  by (oc_eval oc_c30_0455)

lemma oc_c30_0456: "oc_sub oc_b30 456"
  by (oc_eval oc_c30_0456)

lemma oc_c30_0457: "oc_sub oc_b30 457"
  by (oc_eval oc_c30_0457)

lemma oc_c30_0458: "oc_sub oc_b30 458"
  by (oc_eval oc_c30_0458)

lemma oc_c30_0459: "oc_sub oc_b30 459"
  by (oc_eval oc_c30_0459)

lemma oc_c30_0460: "oc_sub oc_b30 460"
  by (oc_eval oc_c30_0460)

lemma oc_c30_0461: "oc_sub oc_b30 461"
  by (oc_eval oc_c30_0461)

lemma oc_c30_0462: "oc_sub oc_b30 462"
  by (oc_eval oc_c30_0462)

lemma oc_c30_0463: "oc_sub oc_b30 463"
  by (oc_eval oc_c30_0463)

lemma upt_c30_028: "[448..<464] = [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]"
  by (simp add: upt_rec)

lemma sec_c30_028: "\<forall>j\<in>{16 * 28..<16 * 28 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 28..<16 * 28 + 16}"
  then have "j \<in> set [448..<464]" unfolding set_upt by simp
  then have "j \<in> set [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]" unfolding upt_c30_028 .
  then show "oc_sub oc_b30 j" using oc_c30_0448 oc_c30_0449 oc_c30_0450 oc_c30_0451 oc_c30_0452 oc_c30_0453 oc_c30_0454 oc_c30_0455 oc_c30_0456 oc_c30_0457 oc_c30_0458 oc_c30_0459 oc_c30_0460 oc_c30_0461 oc_c30_0462 oc_c30_0463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
