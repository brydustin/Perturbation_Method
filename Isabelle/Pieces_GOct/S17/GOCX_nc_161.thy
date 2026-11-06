theory GOCX_nc_161
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2576: "goc_sub None 2576"
  by (goc_eval goc_nc_2576)

lemma goc_nc_2577: "goc_sub None 2577"
  by (goc_eval goc_nc_2577)

lemma goc_nc_2578: "goc_sub None 2578"
  by (goc_eval goc_nc_2578)

lemma goc_nc_2579: "goc_sub None 2579"
  by (goc_eval goc_nc_2579)

lemma goc_nc_2580: "goc_sub None 2580"
  by (goc_eval goc_nc_2580)

lemma goc_nc_2581: "goc_sub None 2581"
  by (goc_eval goc_nc_2581)

lemma goc_nc_2582: "goc_sub None 2582"
  by (goc_eval goc_nc_2582)

lemma goc_nc_2583: "goc_sub None 2583"
  by (goc_eval goc_nc_2583)

lemma goc_nc_2584: "goc_sub None 2584"
  by (goc_eval goc_nc_2584)

lemma goc_nc_2585: "goc_sub None 2585"
  by (goc_eval goc_nc_2585)

lemma goc_nc_2586: "goc_sub None 2586"
  by (goc_eval goc_nc_2586)

lemma goc_nc_2587: "goc_sub None 2587"
  by (goc_eval goc_nc_2587)

lemma goc_nc_2588: "goc_sub None 2588"
  by (goc_eval goc_nc_2588)

lemma goc_nc_2589: "goc_sub None 2589"
  by (goc_eval goc_nc_2589)

lemma goc_nc_2590: "goc_sub None 2590"
  by (goc_eval goc_nc_2590)

lemma goc_nc_2591: "goc_sub None 2591"
  by (goc_eval goc_nc_2591)

lemma gupt_nc_161: "[2576..<2592] = [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]"
  by (simp add: upt_rec)

lemma gsec_nc_161: "\<forall>j\<in>{16 * 161..<16 * 161 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 161..<16 * 161 + 16}"
  then have "j \<in> set [2576..<2592]" unfolding set_upt by simp
  then have "j \<in> set [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]" unfolding gupt_nc_161 .
  then show "goc_sub None j" using goc_nc_2576 goc_nc_2577 goc_nc_2578 goc_nc_2579 goc_nc_2580 goc_nc_2581 goc_nc_2582 goc_nc_2583 goc_nc_2584 goc_nc_2585 goc_nc_2586 goc_nc_2587 goc_nc_2588 goc_nc_2589 goc_nc_2590 goc_nc_2591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
