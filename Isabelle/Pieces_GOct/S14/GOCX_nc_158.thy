theory GOCX_nc_158
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2528: "goc_sub None 2528"
  by (goc_eval goc_nc_2528)

lemma goc_nc_2529: "goc_sub None 2529"
  by (goc_eval goc_nc_2529)

lemma goc_nc_2530: "goc_sub None 2530"
  by (goc_eval goc_nc_2530)

lemma goc_nc_2531: "goc_sub None 2531"
  by (goc_eval goc_nc_2531)

lemma goc_nc_2532: "goc_sub None 2532"
  by (goc_eval goc_nc_2532)

lemma goc_nc_2533: "goc_sub None 2533"
  by (goc_eval goc_nc_2533)

lemma goc_nc_2534: "goc_sub None 2534"
  by (goc_eval goc_nc_2534)

lemma goc_nc_2535: "goc_sub None 2535"
  by (goc_eval goc_nc_2535)

lemma goc_nc_2536: "goc_sub None 2536"
  by (goc_eval goc_nc_2536)

lemma goc_nc_2537: "goc_sub None 2537"
  by (goc_eval goc_nc_2537)

lemma goc_nc_2538: "goc_sub None 2538"
  by (goc_eval goc_nc_2538)

lemma goc_nc_2539: "goc_sub None 2539"
  by (goc_eval goc_nc_2539)

lemma goc_nc_2540: "goc_sub None 2540"
  by (goc_eval goc_nc_2540)

lemma goc_nc_2541: "goc_sub None 2541"
  by (goc_eval goc_nc_2541)

lemma goc_nc_2542: "goc_sub None 2542"
  by (goc_eval goc_nc_2542)

lemma goc_nc_2543: "goc_sub None 2543"
  by (goc_eval goc_nc_2543)

lemma gupt_nc_158: "[2528..<2544] = [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]"
  by (simp add: upt_rec)

lemma gsec_nc_158: "\<forall>j\<in>{16 * 158..<16 * 158 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 158..<16 * 158 + 16}"
  then have "j \<in> set [2528..<2544]" unfolding set_upt by simp
  then have "j \<in> set [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]" unfolding gupt_nc_158 .
  then show "goc_sub None j" using goc_nc_2528 goc_nc_2529 goc_nc_2530 goc_nc_2531 goc_nc_2532 goc_nc_2533 goc_nc_2534 goc_nc_2535 goc_nc_2536 goc_nc_2537 goc_nc_2538 goc_nc_2539 goc_nc_2540 goc_nc_2541 goc_nc_2542 goc_nc_2543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
