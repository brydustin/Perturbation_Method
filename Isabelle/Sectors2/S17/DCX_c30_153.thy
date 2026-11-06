theory DCX_c30_153
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2448: "dc_sub dc_b30 2448"
  by (dc_eval dc_c30_2448)

lemma dc_c30_2449: "dc_sub dc_b30 2449"
  by (dc_eval dc_c30_2449)

lemma dc_c30_2450: "dc_sub dc_b30 2450"
  by (dc_eval dc_c30_2450)

lemma dc_c30_2451: "dc_sub dc_b30 2451"
  by (dc_eval dc_c30_2451)

lemma dc_c30_2452: "dc_sub dc_b30 2452"
  by (dc_eval dc_c30_2452)

lemma dc_c30_2453: "dc_sub dc_b30 2453"
  by (dc_eval dc_c30_2453)

lemma dc_c30_2454: "dc_sub dc_b30 2454"
  by (dc_eval dc_c30_2454)

lemma dc_c30_2455: "dc_sub dc_b30 2455"
  by (dc_eval dc_c30_2455)

lemma dc_c30_2456: "dc_sub dc_b30 2456"
  by (dc_eval dc_c30_2456)

lemma dc_c30_2457: "dc_sub dc_b30 2457"
  by (dc_eval dc_c30_2457)

lemma dc_c30_2458: "dc_sub dc_b30 2458"
  by (dc_eval dc_c30_2458)

lemma dc_c30_2459: "dc_sub dc_b30 2459"
  by (dc_eval dc_c30_2459)

lemma dc_c30_2460: "dc_sub dc_b30 2460"
  by (dc_eval dc_c30_2460)

lemma dc_c30_2461: "dc_sub dc_b30 2461"
  by (dc_eval dc_c30_2461)

lemma dc_c30_2462: "dc_sub dc_b30 2462"
  by (dc_eval dc_c30_2462)

lemma dc_c30_2463: "dc_sub dc_b30 2463"
  by (dc_eval dc_c30_2463)

lemma upt_c30_153: "[2448..<2464] = [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]"
  by (simp add: upt_rec)

lemma sec_c30_153: "\<forall>j\<in>{16 * 153..<16 * 153 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 153..<16 * 153 + 16}"
  then have "j \<in> set [2448..<2464]" unfolding set_upt by simp
  then have "j \<in> set [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]" unfolding upt_c30_153 .
  then show "dc_sub dc_b30 j" using dc_c30_2448 dc_c30_2449 dc_c30_2450 dc_c30_2451 dc_c30_2452 dc_c30_2453 dc_c30_2454 dc_c30_2455 dc_c30_2456 dc_c30_2457 dc_c30_2458 dc_c30_2459 dc_c30_2460 dc_c30_2461 dc_c30_2462 dc_c30_2463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
