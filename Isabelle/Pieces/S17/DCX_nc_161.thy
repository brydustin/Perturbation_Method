theory DCX_nc_161
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2576: "dc_sub None 2576"
  by (dc_eval dc_nc_2576)

lemma dc_nc_2577: "dc_sub None 2577"
  by (dc_eval dc_nc_2577)

lemma dc_nc_2578: "dc_sub None 2578"
  by (dc_eval dc_nc_2578)

lemma dc_nc_2579: "dc_sub None 2579"
  by (dc_eval dc_nc_2579)

lemma dc_nc_2580: "dc_sub None 2580"
  by (dc_eval dc_nc_2580)

lemma dc_nc_2581: "dc_sub None 2581"
  by (dc_eval dc_nc_2581)

lemma dc_nc_2582: "dc_sub None 2582"
  by (dc_eval dc_nc_2582)

lemma dc_nc_2583: "dc_sub None 2583"
  by (dc_eval dc_nc_2583)

lemma dc_nc_2584: "dc_sub None 2584"
  by (dc_eval dc_nc_2584)

lemma dc_nc_2585: "dc_sub None 2585"
  by (dc_eval dc_nc_2585)

lemma dc_nc_2586: "dc_sub None 2586"
  by (dc_eval dc_nc_2586)

lemma dc_nc_2587: "dc_sub None 2587"
  by (dc_eval dc_nc_2587)

lemma dc_nc_2588: "dc_sub None 2588"
  by (dc_eval dc_nc_2588)

lemma dc_nc_2589: "dc_sub None 2589"
  by (dc_eval dc_nc_2589)

lemma dc_nc_2590: "dc_sub None 2590"
  by (dc_eval dc_nc_2590)

lemma dc_nc_2591: "dc_sub None 2591"
  by (dc_eval dc_nc_2591)

lemma upt_nc_161: "[2576..<2592] = [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]"
  by (simp add: upt_rec)

lemma sec_nc_161: "\<forall>j\<in>{16 * 161..<16 * 161 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 161..<16 * 161 + 16}"
  then have "j \<in> set [2576..<2592]" unfolding set_upt by simp
  then have "j \<in> set [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]" unfolding upt_nc_161 .
  then show "dc_sub None j" using dc_nc_2576 dc_nc_2577 dc_nc_2578 dc_nc_2579 dc_nc_2580 dc_nc_2581 dc_nc_2582 dc_nc_2583 dc_nc_2584 dc_nc_2585 dc_nc_2586 dc_nc_2587 dc_nc_2588 dc_nc_2589 dc_nc_2590 dc_nc_2591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
