theory OCX_c30_155
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2480: "oc_sub oc_b30 2480"
  by (oc_eval oc_c30_2480)

lemma oc_c30_2481: "oc_sub oc_b30 2481"
  by (oc_eval oc_c30_2481)

lemma oc_c30_2482: "oc_sub oc_b30 2482"
  by (oc_eval oc_c30_2482)

lemma oc_c30_2483: "oc_sub oc_b30 2483"
  by (oc_eval oc_c30_2483)

lemma oc_c30_2484: "oc_sub oc_b30 2484"
  by (oc_eval oc_c30_2484)

lemma oc_c30_2485: "oc_sub oc_b30 2485"
  by (oc_eval oc_c30_2485)

lemma oc_c30_2486: "oc_sub oc_b30 2486"
  by (oc_eval oc_c30_2486)

lemma oc_c30_2487: "oc_sub oc_b30 2487"
  by (oc_eval oc_c30_2487)

lemma oc_c30_2488: "oc_sub oc_b30 2488"
  by (oc_eval oc_c30_2488)

lemma oc_c30_2489: "oc_sub oc_b30 2489"
  by (oc_eval oc_c30_2489)

lemma oc_c30_2490: "oc_sub oc_b30 2490"
  by (oc_eval oc_c30_2490)

lemma oc_c30_2491: "oc_sub oc_b30 2491"
  by (oc_eval oc_c30_2491)

lemma oc_c30_2492: "oc_sub oc_b30 2492"
  by (oc_eval oc_c30_2492)

lemma oc_c30_2493: "oc_sub oc_b30 2493"
  by (oc_eval oc_c30_2493)

lemma oc_c30_2494: "oc_sub oc_b30 2494"
  by (oc_eval oc_c30_2494)

lemma oc_c30_2495: "oc_sub oc_b30 2495"
  by (oc_eval oc_c30_2495)

lemma upt_c30_155: "[2480..<2496] = [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]"
  by (simp add: upt_rec)

lemma sec_c30_155: "\<forall>j\<in>{16 * 155..<16 * 155 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 155..<16 * 155 + 16}"
  then have "j \<in> set [2480..<2496]" unfolding set_upt by simp
  then have "j \<in> set [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]" unfolding upt_c30_155 .
  then show "oc_sub oc_b30 j" using oc_c30_2480 oc_c30_2481 oc_c30_2482 oc_c30_2483 oc_c30_2484 oc_c30_2485 oc_c30_2486 oc_c30_2487 oc_c30_2488 oc_c30_2489 oc_c30_2490 oc_c30_2491 oc_c30_2492 oc_c30_2493 oc_c30_2494 oc_c30_2495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
