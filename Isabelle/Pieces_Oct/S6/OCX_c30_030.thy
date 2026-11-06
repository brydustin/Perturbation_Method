theory OCX_c30_030
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0480: "oc_sub oc_b30 480"
  by (oc_eval oc_c30_0480)

lemma oc_c30_0481: "oc_sub oc_b30 481"
  by (oc_eval oc_c30_0481)

lemma oc_c30_0482: "oc_sub oc_b30 482"
  by (oc_eval oc_c30_0482)

lemma oc_c30_0483: "oc_sub oc_b30 483"
  by (oc_eval oc_c30_0483)

lemma oc_c30_0484: "oc_sub oc_b30 484"
  by (oc_eval oc_c30_0484)

lemma oc_c30_0485: "oc_sub oc_b30 485"
  by (oc_eval oc_c30_0485)

lemma oc_c30_0486: "oc_sub oc_b30 486"
  by (oc_eval oc_c30_0486)

lemma oc_c30_0487: "oc_sub oc_b30 487"
  by (oc_eval oc_c30_0487)

lemma oc_c30_0488: "oc_sub oc_b30 488"
  by (oc_eval oc_c30_0488)

lemma oc_c30_0489: "oc_sub oc_b30 489"
  by (oc_eval oc_c30_0489)

lemma oc_c30_0490: "oc_sub oc_b30 490"
  by (oc_eval oc_c30_0490)

lemma oc_c30_0491: "oc_sub oc_b30 491"
  by (oc_eval oc_c30_0491)

lemma oc_c30_0492: "oc_sub oc_b30 492"
  by (oc_eval oc_c30_0492)

lemma oc_c30_0493: "oc_sub oc_b30 493"
  by (oc_eval oc_c30_0493)

lemma oc_c30_0494: "oc_sub oc_b30 494"
  by (oc_eval oc_c30_0494)

lemma oc_c30_0495: "oc_sub oc_b30 495"
  by (oc_eval oc_c30_0495)

lemma upt_c30_030: "[480..<496] = [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]"
  by (simp add: upt_rec)

lemma sec_c30_030: "\<forall>j\<in>{16 * 30..<16 * 30 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 30..<16 * 30 + 16}"
  then have "j \<in> set [480..<496]" unfolding set_upt by simp
  then have "j \<in> set [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]" unfolding upt_c30_030 .
  then show "oc_sub oc_b30 j" using oc_c30_0480 oc_c30_0481 oc_c30_0482 oc_c30_0483 oc_c30_0484 oc_c30_0485 oc_c30_0486 oc_c30_0487 oc_c30_0488 oc_c30_0489 oc_c30_0490 oc_c30_0491 oc_c30_0492 oc_c30_0493 oc_c30_0494 oc_c30_0495
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
