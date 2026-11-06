theory DCX_nc_158
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2528: "dc_sub None 2528"
  by (dc_eval dc_nc_2528)

lemma dc_nc_2529: "dc_sub None 2529"
  by (dc_eval dc_nc_2529)

lemma dc_nc_2530: "dc_sub None 2530"
  by (dc_eval dc_nc_2530)

lemma dc_nc_2531: "dc_sub None 2531"
  by (dc_eval dc_nc_2531)

lemma dc_nc_2532: "dc_sub None 2532"
  by (dc_eval dc_nc_2532)

lemma dc_nc_2533: "dc_sub None 2533"
  by (dc_eval dc_nc_2533)

lemma dc_nc_2534: "dc_sub None 2534"
  by (dc_eval dc_nc_2534)

lemma dc_nc_2535: "dc_sub None 2535"
  by (dc_eval dc_nc_2535)

lemma dc_nc_2536: "dc_sub None 2536"
  by (dc_eval dc_nc_2536)

lemma dc_nc_2537: "dc_sub None 2537"
  by (dc_eval dc_nc_2537)

lemma dc_nc_2538: "dc_sub None 2538"
  by (dc_eval dc_nc_2538)

lemma dc_nc_2539: "dc_sub None 2539"
  by (dc_eval dc_nc_2539)

lemma dc_nc_2540: "dc_sub None 2540"
  by (dc_eval dc_nc_2540)

lemma dc_nc_2541: "dc_sub None 2541"
  by (dc_eval dc_nc_2541)

lemma dc_nc_2542: "dc_sub None 2542"
  by (dc_eval dc_nc_2542)

lemma dc_nc_2543: "dc_sub None 2543"
  by (dc_eval dc_nc_2543)

lemma upt_nc_158: "[2528..<2544] = [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]"
  by (simp add: upt_rec)

lemma sec_nc_158: "\<forall>j\<in>{16 * 158..<16 * 158 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 158..<16 * 158 + 16}"
  then have "j \<in> set [2528..<2544]" unfolding set_upt by simp
  then have "j \<in> set [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]" unfolding upt_nc_158 .
  then show "dc_sub None j" using dc_nc_2528 dc_nc_2529 dc_nc_2530 dc_nc_2531 dc_nc_2532 dc_nc_2533 dc_nc_2534 dc_nc_2535 dc_nc_2536 dc_nc_2537 dc_nc_2538 dc_nc_2539 dc_nc_2540 dc_nc_2541 dc_nc_2542 dc_nc_2543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
