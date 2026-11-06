theory DCX_nc_028
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0448: "dc_sub None 448"
  by (dc_eval dc_nc_0448)

lemma dc_nc_0449: "dc_sub None 449"
  by (dc_eval dc_nc_0449)

lemma dc_nc_0450: "dc_sub None 450"
  by (dc_eval dc_nc_0450)

lemma dc_nc_0451: "dc_sub None 451"
  by (dc_eval dc_nc_0451)

lemma dc_nc_0452: "dc_sub None 452"
  by (dc_eval dc_nc_0452)

lemma dc_nc_0453: "dc_sub None 453"
  by (dc_eval dc_nc_0453)

lemma dc_nc_0454: "dc_sub None 454"
  by (dc_eval dc_nc_0454)

lemma dc_nc_0455: "dc_sub None 455"
  by (dc_eval dc_nc_0455)

lemma dc_nc_0456: "dc_sub None 456"
  by (dc_eval dc_nc_0456)

lemma dc_nc_0457: "dc_sub None 457"
  by (dc_eval dc_nc_0457)

lemma dc_nc_0458: "dc_sub None 458"
  by (dc_eval dc_nc_0458)

lemma dc_nc_0459: "dc_sub None 459"
  by (dc_eval dc_nc_0459)

lemma dc_nc_0460: "dc_sub None 460"
  by (dc_eval dc_nc_0460)

lemma dc_nc_0461: "dc_sub None 461"
  by (dc_eval dc_nc_0461)

lemma dc_nc_0462: "dc_sub None 462"
  by (dc_eval dc_nc_0462)

lemma dc_nc_0463: "dc_sub None 463"
  by (dc_eval dc_nc_0463)

lemma upt_nc_028: "[448..<464] = [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]"
  by (simp add: upt_rec)

lemma sec_nc_028: "\<forall>j\<in>{16 * 28..<16 * 28 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 28..<16 * 28 + 16}"
  then have "j \<in> set [448..<464]" unfolding set_upt by simp
  then have "j \<in> set [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]" unfolding upt_nc_028 .
  then show "dc_sub None j" using dc_nc_0448 dc_nc_0449 dc_nc_0450 dc_nc_0451 dc_nc_0452 dc_nc_0453 dc_nc_0454 dc_nc_0455 dc_nc_0456 dc_nc_0457 dc_nc_0458 dc_nc_0459 dc_nc_0460 dc_nc_0461 dc_nc_0462 dc_nc_0463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
