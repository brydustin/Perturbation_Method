theory OCX_nc_155
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2480: "oc_sub None 2480"
  by (oc_eval oc_nc_2480)

lemma oc_nc_2481: "oc_sub None 2481"
  by (oc_eval oc_nc_2481)

lemma oc_nc_2482: "oc_sub None 2482"
  by (oc_eval oc_nc_2482)

lemma oc_nc_2483: "oc_sub None 2483"
  by (oc_eval oc_nc_2483)

lemma oc_nc_2484: "oc_sub None 2484"
  by (oc_eval oc_nc_2484)

lemma oc_nc_2485: "oc_sub None 2485"
  by (oc_eval oc_nc_2485)

lemma oc_nc_2486: "oc_sub None 2486"
  by (oc_eval oc_nc_2486)

lemma oc_nc_2487: "oc_sub None 2487"
  by (oc_eval oc_nc_2487)

lemma oc_nc_2488: "oc_sub None 2488"
  by (oc_eval oc_nc_2488)

lemma oc_nc_2489: "oc_sub None 2489"
  by (oc_eval oc_nc_2489)

lemma oc_nc_2490: "oc_sub None 2490"
  by (oc_eval oc_nc_2490)

lemma oc_nc_2491: "oc_sub None 2491"
  by (oc_eval oc_nc_2491)

lemma oc_nc_2492: "oc_sub None 2492"
  by (oc_eval oc_nc_2492)

lemma oc_nc_2493: "oc_sub None 2493"
  by (oc_eval oc_nc_2493)

lemma oc_nc_2494: "oc_sub None 2494"
  by (oc_eval oc_nc_2494)

lemma oc_nc_2495: "oc_sub None 2495"
  by (oc_eval oc_nc_2495)

lemma upt_nc_155: "[2480..<2496] = [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]"
  by (simp add: upt_rec)

lemma sec_nc_155: "\<forall>j\<in>{16 * 155..<16 * 155 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 155..<16 * 155 + 16}"
  then have "j \<in> set [2480..<2496]" unfolding set_upt by simp
  then have "j \<in> set [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]" unfolding upt_nc_155 .
  then show "oc_sub None j" using oc_nc_2480 oc_nc_2481 oc_nc_2482 oc_nc_2483 oc_nc_2484 oc_nc_2485 oc_nc_2486 oc_nc_2487 oc_nc_2488 oc_nc_2489 oc_nc_2490 oc_nc_2491 oc_nc_2492 oc_nc_2493 oc_nc_2494 oc_nc_2495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
