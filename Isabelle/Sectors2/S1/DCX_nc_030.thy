theory DCX_nc_030
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0480: "dc_sub None 480"
  by (dc_eval dc_nc_0480)

lemma dc_nc_0481: "dc_sub None 481"
  by (dc_eval dc_nc_0481)

lemma dc_nc_0482: "dc_sub None 482"
  by (dc_eval dc_nc_0482)

lemma dc_nc_0483: "dc_sub None 483"
  by (dc_eval dc_nc_0483)

lemma dc_nc_0484: "dc_sub None 484"
  by (dc_eval dc_nc_0484)

lemma dc_nc_0485: "dc_sub None 485"
  by (dc_eval dc_nc_0485)

lemma dc_nc_0486: "dc_sub None 486"
  by (dc_eval dc_nc_0486)

lemma dc_nc_0487: "dc_sub None 487"
  by (dc_eval dc_nc_0487)

lemma dc_nc_0488: "dc_sub None 488"
  by (dc_eval dc_nc_0488)

lemma dc_nc_0489: "dc_sub None 489"
  by (dc_eval dc_nc_0489)

lemma dc_nc_0490: "dc_sub None 490"
  by (dc_eval dc_nc_0490)

lemma dc_nc_0491: "dc_sub None 491"
  by (dc_eval dc_nc_0491)

lemma dc_nc_0492: "dc_sub None 492"
  by (dc_eval dc_nc_0492)

lemma dc_nc_0493: "dc_sub None 493"
  by (dc_eval dc_nc_0493)

lemma dc_nc_0494: "dc_sub None 494"
  by (dc_eval dc_nc_0494)

lemma dc_nc_0495: "dc_sub None 495"
  by (dc_eval dc_nc_0495)

lemma upt_nc_030: "[480..<496] = [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]"
  by (simp add: upt_rec)

lemma sec_nc_030: "\<forall>j\<in>{16 * 30..<16 * 30 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 30..<16 * 30 + 16}"
  then have "j \<in> set [480..<496]" unfolding set_upt by simp
  then have "j \<in> set [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]" unfolding upt_nc_030 .
  then show "dc_sub None j" using dc_nc_0480 dc_nc_0481 dc_nc_0482 dc_nc_0483 dc_nc_0484 dc_nc_0485 dc_nc_0486 dc_nc_0487 dc_nc_0488 dc_nc_0489 dc_nc_0490 dc_nc_0491 dc_nc_0492 dc_nc_0493 dc_nc_0494 dc_nc_0495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
