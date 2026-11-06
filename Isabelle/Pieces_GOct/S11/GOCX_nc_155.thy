theory GOCX_nc_155
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2480: "goc_sub None 2480"
  by (goc_eval goc_nc_2480)

lemma goc_nc_2481: "goc_sub None 2481"
  by (goc_eval goc_nc_2481)

lemma goc_nc_2482: "goc_sub None 2482"
  by (goc_eval goc_nc_2482)

lemma goc_nc_2483: "goc_sub None 2483"
  by (goc_eval goc_nc_2483)

lemma goc_nc_2484: "goc_sub None 2484"
  by (goc_eval goc_nc_2484)

lemma goc_nc_2485: "goc_sub None 2485"
  by (goc_eval goc_nc_2485)

lemma goc_nc_2486: "goc_sub None 2486"
  by (goc_eval goc_nc_2486)

lemma goc_nc_2487: "goc_sub None 2487"
  by (goc_eval goc_nc_2487)

lemma goc_nc_2488: "goc_sub None 2488"
  by (goc_eval goc_nc_2488)

lemma goc_nc_2489: "goc_sub None 2489"
  by (goc_eval goc_nc_2489)

lemma goc_nc_2490: "goc_sub None 2490"
  by (goc_eval goc_nc_2490)

lemma goc_nc_2491: "goc_sub None 2491"
  by (goc_eval goc_nc_2491)

lemma goc_nc_2492: "goc_sub None 2492"
  by (goc_eval goc_nc_2492)

lemma goc_nc_2493: "goc_sub None 2493"
  by (goc_eval goc_nc_2493)

lemma goc_nc_2494: "goc_sub None 2494"
  by (goc_eval goc_nc_2494)

lemma goc_nc_2495: "goc_sub None 2495"
  by (goc_eval goc_nc_2495)

lemma gupt_nc_155: "[2480..<2496] = [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]"
  by (simp add: upt_rec)

lemma gsec_nc_155: "\<forall>j\<in>{16 * 155..<16 * 155 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 155..<16 * 155 + 16}"
  then have "j \<in> set [2480..<2496]" unfolding set_upt by simp
  then have "j \<in> set [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]" unfolding gupt_nc_155 .
  then show "goc_sub None j" using goc_nc_2480 goc_nc_2481 goc_nc_2482 goc_nc_2483 goc_nc_2484 goc_nc_2485 goc_nc_2486 goc_nc_2487 goc_nc_2488 goc_nc_2489 goc_nc_2490 goc_nc_2491 goc_nc_2492 goc_nc_2493 goc_nc_2494 goc_nc_2495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
