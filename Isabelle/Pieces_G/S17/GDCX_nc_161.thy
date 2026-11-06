theory GDCX_nc_161
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2576: "gdc_sub None 2576"
  by (gdc_eval gdc_nc_2576)

lemma gdc_nc_2577: "gdc_sub None 2577"
  by (gdc_eval gdc_nc_2577)

lemma gdc_nc_2578: "gdc_sub None 2578"
  by (gdc_eval gdc_nc_2578)

lemma gdc_nc_2579: "gdc_sub None 2579"
  by (gdc_eval gdc_nc_2579)

lemma gdc_nc_2580: "gdc_sub None 2580"
  by (gdc_eval gdc_nc_2580)

lemma gdc_nc_2581: "gdc_sub None 2581"
  by (gdc_eval gdc_nc_2581)

lemma gdc_nc_2582: "gdc_sub None 2582"
  by (gdc_eval gdc_nc_2582)

lemma gdc_nc_2583: "gdc_sub None 2583"
  by (gdc_eval gdc_nc_2583)

lemma gdc_nc_2584: "gdc_sub None 2584"
  by (gdc_eval gdc_nc_2584)

lemma gdc_nc_2585: "gdc_sub None 2585"
  by (gdc_eval gdc_nc_2585)

lemma gdc_nc_2586: "gdc_sub None 2586"
  by (gdc_eval gdc_nc_2586)

lemma gdc_nc_2587: "gdc_sub None 2587"
  by (gdc_eval gdc_nc_2587)

lemma gdc_nc_2588: "gdc_sub None 2588"
  by (gdc_eval gdc_nc_2588)

lemma gdc_nc_2589: "gdc_sub None 2589"
  by (gdc_eval gdc_nc_2589)

lemma gdc_nc_2590: "gdc_sub None 2590"
  by (gdc_eval gdc_nc_2590)

lemma gdc_nc_2591: "gdc_sub None 2591"
  by (gdc_eval gdc_nc_2591)

lemma gupt_nc_161: "[2576..<2592] = [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]"
  by (simp add: upt_rec)

lemma gsec_nc_161: "\<forall>j\<in>{16 * 161..<16 * 161 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 161..<16 * 161 + 16}"
  then have "j \<in> set [2576..<2592]" unfolding set_upt by simp
  then have "j \<in> set [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]" unfolding gupt_nc_161 .
  then show "gdc_sub None j" using gdc_nc_2576 gdc_nc_2577 gdc_nc_2578 gdc_nc_2579 gdc_nc_2580 gdc_nc_2581 gdc_nc_2582 gdc_nc_2583 gdc_nc_2584 gdc_nc_2585 gdc_nc_2586 gdc_nc_2587 gdc_nc_2588 gdc_nc_2589 gdc_nc_2590 gdc_nc_2591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
