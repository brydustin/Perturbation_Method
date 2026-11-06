theory OCX_c30_161
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2576: "oc_sub oc_b30 2576"
  by (oc_eval oc_c30_2576)

lemma oc_c30_2577: "oc_sub oc_b30 2577"
  by (oc_eval oc_c30_2577)

lemma oc_c30_2578: "oc_sub oc_b30 2578"
  by (oc_eval oc_c30_2578)

lemma oc_c30_2579: "oc_sub oc_b30 2579"
  by (oc_eval oc_c30_2579)

lemma oc_c30_2580: "oc_sub oc_b30 2580"
  by (oc_eval oc_c30_2580)

lemma oc_c30_2581: "oc_sub oc_b30 2581"
  by (oc_eval oc_c30_2581)

lemma oc_c30_2582: "oc_sub oc_b30 2582"
  by (oc_eval oc_c30_2582)

lemma oc_c30_2583: "oc_sub oc_b30 2583"
  by (oc_eval oc_c30_2583)

lemma oc_c30_2584: "oc_sub oc_b30 2584"
  by (oc_eval oc_c30_2584)

lemma oc_c30_2585: "oc_sub oc_b30 2585"
  by (oc_eval oc_c30_2585)

lemma oc_c30_2586: "oc_sub oc_b30 2586"
  by (oc_eval oc_c30_2586)

lemma oc_c30_2587: "oc_sub oc_b30 2587"
  by (oc_eval oc_c30_2587)

lemma oc_c30_2588: "oc_sub oc_b30 2588"
  by (oc_eval oc_c30_2588)

lemma oc_c30_2589: "oc_sub oc_b30 2589"
  by (oc_eval oc_c30_2589)

lemma oc_c30_2590: "oc_sub oc_b30 2590"
  by (oc_eval oc_c30_2590)

lemma oc_c30_2591: "oc_sub oc_b30 2591"
  by (oc_eval oc_c30_2591)

lemma upt_c30_161: "[2576..<2592] = [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]"
  by (simp add: upt_rec)

lemma sec_c30_161: "\<forall>j\<in>{16 * 161..<16 * 161 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 161..<16 * 161 + 16}"
  then have "j \<in> set [2576..<2592]" unfolding set_upt by simp
  then have "j \<in> set [2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2589, 2590, 2591]" unfolding upt_c30_161 .
  then show "oc_sub oc_b30 j" using oc_c30_2576 oc_c30_2577 oc_c30_2578 oc_c30_2579 oc_c30_2580 oc_c30_2581 oc_c30_2582 oc_c30_2583 oc_c30_2584 oc_c30_2585 oc_c30_2586 oc_c30_2587 oc_c30_2588 oc_c30_2589 oc_c30_2590 oc_c30_2591
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
