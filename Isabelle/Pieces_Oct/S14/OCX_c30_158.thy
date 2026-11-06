theory OCX_c30_158
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2528: "oc_sub oc_b30 2528"
  by (oc_eval oc_c30_2528)

lemma oc_c30_2529: "oc_sub oc_b30 2529"
  by (oc_eval oc_c30_2529)

lemma oc_c30_2530: "oc_sub oc_b30 2530"
  by (oc_eval oc_c30_2530)

lemma oc_c30_2531: "oc_sub oc_b30 2531"
  by (oc_eval oc_c30_2531)

lemma oc_c30_2532: "oc_sub oc_b30 2532"
  by (oc_eval oc_c30_2532)

lemma oc_c30_2533: "oc_sub oc_b30 2533"
  by (oc_eval oc_c30_2533)

lemma oc_c30_2534: "oc_sub oc_b30 2534"
  by (oc_eval oc_c30_2534)

lemma oc_c30_2535: "oc_sub oc_b30 2535"
  by (oc_eval oc_c30_2535)

lemma oc_c30_2536: "oc_sub oc_b30 2536"
  by (oc_eval oc_c30_2536)

lemma oc_c30_2537: "oc_sub oc_b30 2537"
  by (oc_eval oc_c30_2537)

lemma oc_c30_2538: "oc_sub oc_b30 2538"
  by (oc_eval oc_c30_2538)

lemma oc_c30_2539: "oc_sub oc_b30 2539"
  by (oc_eval oc_c30_2539)

lemma oc_c30_2540: "oc_sub oc_b30 2540"
  by (oc_eval oc_c30_2540)

lemma oc_c30_2541: "oc_sub oc_b30 2541"
  by (oc_eval oc_c30_2541)

lemma oc_c30_2542: "oc_sub oc_b30 2542"
  by (oc_eval oc_c30_2542)

lemma oc_c30_2543: "oc_sub oc_b30 2543"
  by (oc_eval oc_c30_2543)

lemma upt_c30_158: "[2528..<2544] = [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]"
  by (simp add: upt_rec)

lemma sec_c30_158: "\<forall>j\<in>{16 * 158..<16 * 158 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 158..<16 * 158 + 16}"
  then have "j \<in> set [2528..<2544]" unfolding set_upt by simp
  then have "j \<in> set [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]" unfolding upt_c30_158 .
  then show "oc_sub oc_b30 j" using oc_c30_2528 oc_c30_2529 oc_c30_2530 oc_c30_2531 oc_c30_2532 oc_c30_2533 oc_c30_2534 oc_c30_2535 oc_c30_2536 oc_c30_2537 oc_c30_2538 oc_c30_2539 oc_c30_2540 oc_c30_2541 oc_c30_2542 oc_c30_2543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
