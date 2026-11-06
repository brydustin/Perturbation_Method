theory DCX_c30_155
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2480: "dc_sub dc_b30 2480"
  by (dc_eval dc_c30_2480)

lemma dc_c30_2481: "dc_sub dc_b30 2481"
  by (dc_eval dc_c30_2481)

lemma dc_c30_2482: "dc_sub dc_b30 2482"
  by (dc_eval dc_c30_2482)

lemma dc_c30_2483: "dc_sub dc_b30 2483"
  by (dc_eval dc_c30_2483)

lemma dc_c30_2484: "dc_sub dc_b30 2484"
  by (dc_eval dc_c30_2484)

lemma dc_c30_2485: "dc_sub dc_b30 2485"
  by (dc_eval dc_c30_2485)

lemma dc_c30_2486: "dc_sub dc_b30 2486"
  by (dc_eval dc_c30_2486)

lemma dc_c30_2487: "dc_sub dc_b30 2487"
  by (dc_eval dc_c30_2487)

lemma dc_c30_2488: "dc_sub dc_b30 2488"
  by (dc_eval dc_c30_2488)

lemma dc_c30_2489: "dc_sub dc_b30 2489"
  by (dc_eval dc_c30_2489)

lemma dc_c30_2490: "dc_sub dc_b30 2490"
  by (dc_eval dc_c30_2490)

lemma dc_c30_2491: "dc_sub dc_b30 2491"
  by (dc_eval dc_c30_2491)

lemma dc_c30_2492: "dc_sub dc_b30 2492"
  by (dc_eval dc_c30_2492)

lemma dc_c30_2493: "dc_sub dc_b30 2493"
  by (dc_eval dc_c30_2493)

lemma dc_c30_2494: "dc_sub dc_b30 2494"
  by (dc_eval dc_c30_2494)

lemma dc_c30_2495: "dc_sub dc_b30 2495"
  by (dc_eval dc_c30_2495)

lemma upt_c30_155: "[2480..<2496] = [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]"
  by (simp add: upt_rec)

lemma sec_c30_155: "\<forall>j\<in>{16 * 155..<16 * 155 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 155..<16 * 155 + 16}"
  then have "j \<in> set [2480..<2496]" unfolding set_upt by simp
  then have "j \<in> set [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]" unfolding upt_c30_155 .
  then show "dc_sub dc_b30 j" using dc_c30_2480 dc_c30_2481 dc_c30_2482 dc_c30_2483 dc_c30_2484 dc_c30_2485 dc_c30_2486 dc_c30_2487 dc_c30_2488 dc_c30_2489 dc_c30_2490 dc_c30_2491 dc_c30_2492 dc_c30_2493 dc_c30_2494 dc_c30_2495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
