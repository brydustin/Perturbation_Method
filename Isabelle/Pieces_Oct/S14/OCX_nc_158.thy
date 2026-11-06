theory OCX_nc_158
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2528: "oc_sub None 2528"
  by (oc_eval oc_nc_2528)

lemma oc_nc_2529: "oc_sub None 2529"
  by (oc_eval oc_nc_2529)

lemma oc_nc_2530: "oc_sub None 2530"
  by (oc_eval oc_nc_2530)

lemma oc_nc_2531: "oc_sub None 2531"
  by (oc_eval oc_nc_2531)

lemma oc_nc_2532: "oc_sub None 2532"
  by (oc_eval oc_nc_2532)

lemma oc_nc_2533: "oc_sub None 2533"
  by (oc_eval oc_nc_2533)

lemma oc_nc_2534: "oc_sub None 2534"
  by (oc_eval oc_nc_2534)

lemma oc_nc_2535: "oc_sub None 2535"
  by (oc_eval oc_nc_2535)

lemma oc_nc_2536: "oc_sub None 2536"
  by (oc_eval oc_nc_2536)

lemma oc_nc_2537: "oc_sub None 2537"
  by (oc_eval oc_nc_2537)

lemma oc_nc_2538: "oc_sub None 2538"
  by (oc_eval oc_nc_2538)

lemma oc_nc_2539: "oc_sub None 2539"
  by (oc_eval oc_nc_2539)

lemma oc_nc_2540: "oc_sub None 2540"
  by (oc_eval oc_nc_2540)

lemma oc_nc_2541: "oc_sub None 2541"
  by (oc_eval oc_nc_2541)

lemma oc_nc_2542: "oc_sub None 2542"
  by (oc_eval oc_nc_2542)

lemma oc_nc_2543: "oc_sub None 2543"
  by (oc_eval oc_nc_2543)

lemma upt_nc_158: "[2528..<2544] = [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]"
  by (simp add: upt_rec)

lemma sec_nc_158: "\<forall>j\<in>{16 * 158..<16 * 158 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 158..<16 * 158 + 16}"
  then have "j \<in> set [2528..<2544]" unfolding set_upt by simp
  then have "j \<in> set [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]" unfolding upt_nc_158 .
  then show "oc_sub None j" using oc_nc_2528 oc_nc_2529 oc_nc_2530 oc_nc_2531 oc_nc_2532 oc_nc_2533 oc_nc_2534 oc_nc_2535 oc_nc_2536 oc_nc_2537 oc_nc_2538 oc_nc_2539 oc_nc_2540 oc_nc_2541 oc_nc_2542 oc_nc_2543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
