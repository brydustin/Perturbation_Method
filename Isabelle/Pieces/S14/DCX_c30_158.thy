theory DCX_c30_158
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2528: "dc_sub dc_b30 2528"
  by (dc_eval dc_c30_2528)

lemma dc_c30_2529: "dc_sub dc_b30 2529"
  by (dc_eval dc_c30_2529)

lemma dc_c30_2530: "dc_sub dc_b30 2530"
  by (dc_eval dc_c30_2530)

lemma dc_c30_2531: "dc_sub dc_b30 2531"
  by (dc_eval dc_c30_2531)

lemma dc_c30_2532: "dc_sub dc_b30 2532"
  by (dc_eval dc_c30_2532)

lemma dc_c30_2533: "dc_sub dc_b30 2533"
  by (dc_eval dc_c30_2533)

lemma dc_c30_2534: "dc_sub dc_b30 2534"
  by (dc_eval dc_c30_2534)

lemma dc_c30_2535: "dc_sub dc_b30 2535"
  by (dc_eval dc_c30_2535)

lemma dc_c30_2536: "dc_sub dc_b30 2536"
  by (dc_eval dc_c30_2536)

lemma dc_c30_2537: "dc_sub dc_b30 2537"
  by (dc_eval dc_c30_2537)

lemma dc_c30_2538: "dc_sub dc_b30 2538"
  by (dc_eval dc_c30_2538)

lemma dc_c30_2539: "dc_sub dc_b30 2539"
  by (dc_eval dc_c30_2539)

lemma dc_c30_2540: "dc_sub dc_b30 2540"
  by (dc_eval dc_c30_2540)

lemma dc_c30_2541: "dc_sub dc_b30 2541"
  by (dc_eval dc_c30_2541)

lemma dc_c30_2542: "dc_sub dc_b30 2542"
  by (dc_eval dc_c30_2542)

lemma dc_c30_2543: "dc_sub dc_b30 2543"
  by (dc_eval dc_c30_2543)

lemma upt_c30_158: "[2528..<2544] = [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]"
  by (simp add: upt_rec)

lemma sec_c30_158: "\<forall>j\<in>{16 * 158..<16 * 158 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 158..<16 * 158 + 16}"
  then have "j \<in> set [2528..<2544]" unfolding set_upt by simp
  then have "j \<in> set [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]" unfolding upt_c30_158 .
  then show "dc_sub dc_b30 j" using dc_c30_2528 dc_c30_2529 dc_c30_2530 dc_c30_2531 dc_c30_2532 dc_c30_2533 dc_c30_2534 dc_c30_2535 dc_c30_2536 dc_c30_2537 dc_c30_2538 dc_c30_2539 dc_c30_2540 dc_c30_2541 dc_c30_2542 dc_c30_2543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
