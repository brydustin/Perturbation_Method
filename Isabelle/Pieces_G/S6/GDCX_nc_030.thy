theory GDCX_nc_030
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0480: "gdc_sub None 480"
  by (gdc_eval gdc_nc_0480)

lemma gdc_nc_0481: "gdc_sub None 481"
  by (gdc_eval gdc_nc_0481)

lemma gdc_nc_0482: "gdc_sub None 482"
  by (gdc_eval gdc_nc_0482)

lemma gdc_nc_0483: "gdc_sub None 483"
  by (gdc_eval gdc_nc_0483)

lemma gdc_nc_0484: "gdc_sub None 484"
  by (gdc_eval gdc_nc_0484)

lemma gdc_nc_0485: "gdc_sub None 485"
  by (gdc_eval gdc_nc_0485)

lemma gdc_nc_0486: "gdc_sub None 486"
  by (gdc_eval gdc_nc_0486)

lemma gdc_nc_0487: "gdc_sub None 487"
  by (gdc_eval gdc_nc_0487)

lemma gdc_nc_0488: "gdc_sub None 488"
  by (gdc_eval gdc_nc_0488)

lemma gdc_nc_0489: "gdc_sub None 489"
  by (gdc_eval gdc_nc_0489)

lemma gdc_nc_0490: "gdc_sub None 490"
  by (gdc_eval gdc_nc_0490)

lemma gdc_nc_0491: "gdc_sub None 491"
  by (gdc_eval gdc_nc_0491)

lemma gdc_nc_0492: "gdc_sub None 492"
  by (gdc_eval gdc_nc_0492)

lemma gdc_nc_0493: "gdc_sub None 493"
  by (gdc_eval gdc_nc_0493)

lemma gdc_nc_0494: "gdc_sub None 494"
  by (gdc_eval gdc_nc_0494)

lemma gdc_nc_0495: "gdc_sub None 495"
  by (gdc_eval gdc_nc_0495)

lemma gupt_nc_030: "[480..<496] = [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]"
  by (simp add: upt_rec)

lemma gsec_nc_030: "\<forall>j\<in>{16 * 30..<16 * 30 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 30..<16 * 30 + 16}"
  then have "j \<in> set [480..<496]" unfolding set_upt by simp
  then have "j \<in> set [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]" unfolding gupt_nc_030 .
  then show "gdc_sub None j" using gdc_nc_0480 gdc_nc_0481 gdc_nc_0482 gdc_nc_0483 gdc_nc_0484 gdc_nc_0485 gdc_nc_0486 gdc_nc_0487 gdc_nc_0488 gdc_nc_0489 gdc_nc_0490 gdc_nc_0491 gdc_nc_0492 gdc_nc_0493 gdc_nc_0494 gdc_nc_0495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
