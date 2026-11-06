theory DCX_c30_028
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0448: "dc_sub dc_b30 448"
  by (dc_eval dc_c30_0448)

lemma dc_c30_0449: "dc_sub dc_b30 449"
  by (dc_eval dc_c30_0449)

lemma dc_c30_0450: "dc_sub dc_b30 450"
  by (dc_eval dc_c30_0450)

lemma dc_c30_0451: "dc_sub dc_b30 451"
  by (dc_eval dc_c30_0451)

lemma dc_c30_0452: "dc_sub dc_b30 452"
  by (dc_eval dc_c30_0452)

lemma dc_c30_0453: "dc_sub dc_b30 453"
  by (dc_eval dc_c30_0453)

lemma dc_c30_0454: "dc_sub dc_b30 454"
  by (dc_eval dc_c30_0454)

lemma dc_c30_0455: "dc_sub dc_b30 455"
  by (dc_eval dc_c30_0455)

lemma dc_c30_0456: "dc_sub dc_b30 456"
  by (dc_eval dc_c30_0456)

lemma dc_c30_0457: "dc_sub dc_b30 457"
  by (dc_eval dc_c30_0457)

lemma dc_c30_0458: "dc_sub dc_b30 458"
  by (dc_eval dc_c30_0458)

lemma dc_c30_0459: "dc_sub dc_b30 459"
  by (dc_eval dc_c30_0459)

lemma dc_c30_0460: "dc_sub dc_b30 460"
  by (dc_eval dc_c30_0460)

lemma dc_c30_0461: "dc_sub dc_b30 461"
  by (dc_eval dc_c30_0461)

lemma dc_c30_0462: "dc_sub dc_b30 462"
  by (dc_eval dc_c30_0462)

lemma dc_c30_0463: "dc_sub dc_b30 463"
  by (dc_eval dc_c30_0463)

lemma upt_c30_028: "[448..<464] = [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]"
  by (simp add: upt_rec)

lemma sec_c30_028: "\<forall>j\<in>{16 * 28..<16 * 28 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 28..<16 * 28 + 16}"
  then have "j \<in> set [448..<464]" unfolding set_upt by simp
  then have "j \<in> set [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]" unfolding upt_c30_028 .
  then show "dc_sub dc_b30 j" using dc_c30_0448 dc_c30_0449 dc_c30_0450 dc_c30_0451 dc_c30_0452 dc_c30_0453 dc_c30_0454 dc_c30_0455 dc_c30_0456 dc_c30_0457 dc_c30_0458 dc_c30_0459 dc_c30_0460 dc_c30_0461 dc_c30_0462 dc_c30_0463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
