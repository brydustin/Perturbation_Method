theory GDCX_nc_155
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2480: "gdc_sub None 2480"
  by (gdc_eval gdc_nc_2480)

lemma gdc_nc_2481: "gdc_sub None 2481"
  by (gdc_eval gdc_nc_2481)

lemma gdc_nc_2482: "gdc_sub None 2482"
  by (gdc_eval gdc_nc_2482)

lemma gdc_nc_2483: "gdc_sub None 2483"
  by (gdc_eval gdc_nc_2483)

lemma gdc_nc_2484: "gdc_sub None 2484"
  by (gdc_eval gdc_nc_2484)

lemma gdc_nc_2485: "gdc_sub None 2485"
  by (gdc_eval gdc_nc_2485)

lemma gdc_nc_2486: "gdc_sub None 2486"
  by (gdc_eval gdc_nc_2486)

lemma gdc_nc_2487: "gdc_sub None 2487"
  by (gdc_eval gdc_nc_2487)

lemma gdc_nc_2488: "gdc_sub None 2488"
  by (gdc_eval gdc_nc_2488)

lemma gdc_nc_2489: "gdc_sub None 2489"
  by (gdc_eval gdc_nc_2489)

lemma gdc_nc_2490: "gdc_sub None 2490"
  by (gdc_eval gdc_nc_2490)

lemma gdc_nc_2491: "gdc_sub None 2491"
  by (gdc_eval gdc_nc_2491)

lemma gdc_nc_2492: "gdc_sub None 2492"
  by (gdc_eval gdc_nc_2492)

lemma gdc_nc_2493: "gdc_sub None 2493"
  by (gdc_eval gdc_nc_2493)

lemma gdc_nc_2494: "gdc_sub None 2494"
  by (gdc_eval gdc_nc_2494)

lemma gdc_nc_2495: "gdc_sub None 2495"
  by (gdc_eval gdc_nc_2495)

lemma gupt_nc_155: "[2480..<2496] = [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]"
  by (simp add: upt_rec)

lemma gsec_nc_155: "\<forall>j\<in>{16 * 155..<16 * 155 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 155..<16 * 155 + 16}"
  then have "j \<in> set [2480..<2496]" unfolding set_upt by simp
  then have "j \<in> set [2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495]" unfolding gupt_nc_155 .
  then show "gdc_sub None j" using gdc_nc_2480 gdc_nc_2481 gdc_nc_2482 gdc_nc_2483 gdc_nc_2484 gdc_nc_2485 gdc_nc_2486 gdc_nc_2487 gdc_nc_2488 gdc_nc_2489 gdc_nc_2490 gdc_nc_2491 gdc_nc_2492 gdc_nc_2493 gdc_nc_2494 gdc_nc_2495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
