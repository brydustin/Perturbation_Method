theory GDCX_nc_158
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2528: "gdc_sub None 2528"
  by (gdc_eval gdc_nc_2528)

lemma gdc_nc_2529: "gdc_sub None 2529"
  by (gdc_eval gdc_nc_2529)

lemma gdc_nc_2530: "gdc_sub None 2530"
  by (gdc_eval gdc_nc_2530)

lemma gdc_nc_2531: "gdc_sub None 2531"
  by (gdc_eval gdc_nc_2531)

lemma gdc_nc_2532: "gdc_sub None 2532"
  by (gdc_eval gdc_nc_2532)

lemma gdc_nc_2533: "gdc_sub None 2533"
  by (gdc_eval gdc_nc_2533)

lemma gdc_nc_2534: "gdc_sub None 2534"
  by (gdc_eval gdc_nc_2534)

lemma gdc_nc_2535: "gdc_sub None 2535"
  by (gdc_eval gdc_nc_2535)

lemma gdc_nc_2536: "gdc_sub None 2536"
  by (gdc_eval gdc_nc_2536)

lemma gdc_nc_2537: "gdc_sub None 2537"
  by (gdc_eval gdc_nc_2537)

lemma gdc_nc_2538: "gdc_sub None 2538"
  by (gdc_eval gdc_nc_2538)

lemma gdc_nc_2539: "gdc_sub None 2539"
  by (gdc_eval gdc_nc_2539)

lemma gdc_nc_2540: "gdc_sub None 2540"
  by (gdc_eval gdc_nc_2540)

lemma gdc_nc_2541: "gdc_sub None 2541"
  by (gdc_eval gdc_nc_2541)

lemma gdc_nc_2542: "gdc_sub None 2542"
  by (gdc_eval gdc_nc_2542)

lemma gdc_nc_2543: "gdc_sub None 2543"
  by (gdc_eval gdc_nc_2543)

lemma gupt_nc_158: "[2528..<2544] = [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]"
  by (simp add: upt_rec)

lemma gsec_nc_158: "\<forall>j\<in>{16 * 158..<16 * 158 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 158..<16 * 158 + 16}"
  then have "j \<in> set [2528..<2544]" unfolding set_upt by simp
  then have "j \<in> set [2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543]" unfolding gupt_nc_158 .
  then show "gdc_sub None j" using gdc_nc_2528 gdc_nc_2529 gdc_nc_2530 gdc_nc_2531 gdc_nc_2532 gdc_nc_2533 gdc_nc_2534 gdc_nc_2535 gdc_nc_2536 gdc_nc_2537 gdc_nc_2538 gdc_nc_2539 gdc_nc_2540 gdc_nc_2541 gdc_nc_2542 gdc_nc_2543
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
