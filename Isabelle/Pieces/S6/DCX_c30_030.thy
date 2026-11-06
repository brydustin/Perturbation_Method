theory DCX_c30_030
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0480: "dc_sub dc_b30 480"
  by (dc_eval dc_c30_0480)

lemma dc_c30_0481: "dc_sub dc_b30 481"
  by (dc_eval dc_c30_0481)

lemma dc_c30_0482: "dc_sub dc_b30 482"
  by (dc_eval dc_c30_0482)

lemma dc_c30_0483: "dc_sub dc_b30 483"
  by (dc_eval dc_c30_0483)

lemma dc_c30_0484: "dc_sub dc_b30 484"
  by (dc_eval dc_c30_0484)

lemma dc_c30_0485: "dc_sub dc_b30 485"
  by (dc_eval dc_c30_0485)

lemma dc_c30_0486: "dc_sub dc_b30 486"
  by (dc_eval dc_c30_0486)

lemma dc_c30_0487: "dc_sub dc_b30 487"
  by (dc_eval dc_c30_0487)

lemma dc_c30_0488: "dc_sub dc_b30 488"
  by (dc_eval dc_c30_0488)

lemma dc_c30_0489: "dc_sub dc_b30 489"
  by (dc_eval dc_c30_0489)

lemma dc_c30_0490: "dc_sub dc_b30 490"
  by (dc_eval dc_c30_0490)

lemma dc_c30_0491: "dc_sub dc_b30 491"
  by (dc_eval dc_c30_0491)

lemma dc_c30_0492: "dc_sub dc_b30 492"
  by (dc_eval dc_c30_0492)

lemma dc_c30_0493: "dc_sub dc_b30 493"
  by (dc_eval dc_c30_0493)

lemma dc_c30_0494: "dc_sub dc_b30 494"
  by (dc_eval dc_c30_0494)

lemma dc_c30_0495: "dc_sub dc_b30 495"
  by (dc_eval dc_c30_0495)

lemma upt_c30_030: "[480..<496] = [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]"
  by (simp add: upt_rec)

lemma sec_c30_030: "\<forall>j\<in>{16 * 30..<16 * 30 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 30..<16 * 30 + 16}"
  then have "j \<in> set [480..<496]" unfolding set_upt by simp
  then have "j \<in> set [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]" unfolding upt_c30_030 .
  then show "dc_sub dc_b30 j" using dc_c30_0480 dc_c30_0481 dc_c30_0482 dc_c30_0483 dc_c30_0484 dc_c30_0485 dc_c30_0486 dc_c30_0487 dc_c30_0488 dc_c30_0489 dc_c30_0490 dc_c30_0491 dc_c30_0492 dc_c30_0493 dc_c30_0494 dc_c30_0495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
