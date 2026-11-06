theory GOCX_nc_030
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0480: "goc_sub None 480"
  by (goc_eval goc_nc_0480)

lemma goc_nc_0481: "goc_sub None 481"
  by (goc_eval goc_nc_0481)

lemma goc_nc_0482: "goc_sub None 482"
  by (goc_eval goc_nc_0482)

lemma goc_nc_0483: "goc_sub None 483"
  by (goc_eval goc_nc_0483)

lemma goc_nc_0484: "goc_sub None 484"
  by (goc_eval goc_nc_0484)

lemma goc_nc_0485: "goc_sub None 485"
  by (goc_eval goc_nc_0485)

lemma goc_nc_0486: "goc_sub None 486"
  by (goc_eval goc_nc_0486)

lemma goc_nc_0487: "goc_sub None 487"
  by (goc_eval goc_nc_0487)

lemma goc_nc_0488: "goc_sub None 488"
  by (goc_eval goc_nc_0488)

lemma goc_nc_0489: "goc_sub None 489"
  by (goc_eval goc_nc_0489)

lemma goc_nc_0490: "goc_sub None 490"
  by (goc_eval goc_nc_0490)

lemma goc_nc_0491: "goc_sub None 491"
  by (goc_eval goc_nc_0491)

lemma goc_nc_0492: "goc_sub None 492"
  by (goc_eval goc_nc_0492)

lemma goc_nc_0493: "goc_sub None 493"
  by (goc_eval goc_nc_0493)

lemma goc_nc_0494: "goc_sub None 494"
  by (goc_eval goc_nc_0494)

lemma goc_nc_0495: "goc_sub None 495"
  by (goc_eval goc_nc_0495)

lemma gupt_nc_030: "[480..<496] = [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]"
  by (simp add: upt_rec)

lemma gsec_nc_030: "\<forall>j\<in>{16 * 30..<16 * 30 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 30..<16 * 30 + 16}"
  then have "j \<in> set [480..<496]" unfolding set_upt by simp
  then have "j \<in> set [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]" unfolding gupt_nc_030 .
  then show "goc_sub None j" using goc_nc_0480 goc_nc_0481 goc_nc_0482 goc_nc_0483 goc_nc_0484 goc_nc_0485 goc_nc_0486 goc_nc_0487 goc_nc_0488 goc_nc_0489 goc_nc_0490 goc_nc_0491 goc_nc_0492 goc_nc_0493 goc_nc_0494 goc_nc_0495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
