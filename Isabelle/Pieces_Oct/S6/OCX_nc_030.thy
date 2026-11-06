theory OCX_nc_030
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0480: "oc_sub None 480"
  by (oc_eval oc_nc_0480)

lemma oc_nc_0481: "oc_sub None 481"
  by (oc_eval oc_nc_0481)

lemma oc_nc_0482: "oc_sub None 482"
  by (oc_eval oc_nc_0482)

lemma oc_nc_0483: "oc_sub None 483"
  by (oc_eval oc_nc_0483)

lemma oc_nc_0484: "oc_sub None 484"
  by (oc_eval oc_nc_0484)

lemma oc_nc_0485: "oc_sub None 485"
  by (oc_eval oc_nc_0485)

lemma oc_nc_0486: "oc_sub None 486"
  by (oc_eval oc_nc_0486)

lemma oc_nc_0487: "oc_sub None 487"
  by (oc_eval oc_nc_0487)

lemma oc_nc_0488: "oc_sub None 488"
  by (oc_eval oc_nc_0488)

lemma oc_nc_0489: "oc_sub None 489"
  by (oc_eval oc_nc_0489)

lemma oc_nc_0490: "oc_sub None 490"
  by (oc_eval oc_nc_0490)

lemma oc_nc_0491: "oc_sub None 491"
  by (oc_eval oc_nc_0491)

lemma oc_nc_0492: "oc_sub None 492"
  by (oc_eval oc_nc_0492)

lemma oc_nc_0493: "oc_sub None 493"
  by (oc_eval oc_nc_0493)

lemma oc_nc_0494: "oc_sub None 494"
  by (oc_eval oc_nc_0494)

lemma oc_nc_0495: "oc_sub None 495"
  by (oc_eval oc_nc_0495)

lemma upt_nc_030: "[480..<496] = [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]"
  by (simp add: upt_rec)

lemma sec_nc_030: "\<forall>j\<in>{16 * 30..<16 * 30 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 30..<16 * 30 + 16}"
  then have "j \<in> set [480..<496]" unfolding set_upt by simp
  then have "j \<in> set [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]" unfolding upt_nc_030 .
  then show "oc_sub None j" using oc_nc_0480 oc_nc_0481 oc_nc_0482 oc_nc_0483 oc_nc_0484 oc_nc_0485 oc_nc_0486 oc_nc_0487 oc_nc_0488 oc_nc_0489 oc_nc_0490 oc_nc_0491 oc_nc_0492 oc_nc_0493 oc_nc_0494 oc_nc_0495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
