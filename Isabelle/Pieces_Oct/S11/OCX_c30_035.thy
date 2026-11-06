theory OCX_c30_035
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0560: "oc_sub oc_b30 560"
  by (oc_eval oc_c30_0560)

lemma oc_c30_0561: "oc_sub oc_b30 561"
  by (oc_eval oc_c30_0561)

lemma oc_c30_0562: "oc_sub oc_b30 562"
  by (oc_eval oc_c30_0562)

lemma oc_c30_0563: "oc_sub oc_b30 563"
  by (oc_eval oc_c30_0563)

lemma oc_c30_0564: "oc_sub oc_b30 564"
  by (oc_eval oc_c30_0564)

lemma oc_c30_0565: "oc_sub oc_b30 565"
  by (oc_eval oc_c30_0565)

lemma oc_c30_0566: "oc_sub oc_b30 566"
  by (oc_eval oc_c30_0566)

lemma oc_c30_0567: "oc_sub oc_b30 567"
  by (oc_eval oc_c30_0567)

lemma oc_c30_0568: "oc_sub oc_b30 568"
  by (oc_eval oc_c30_0568)

lemma oc_c30_0569: "oc_sub oc_b30 569"
  by (oc_eval oc_c30_0569)

lemma oc_c30_0570: "oc_sub oc_b30 570"
  by (oc_eval oc_c30_0570)

lemma oc_c30_0571: "oc_sub oc_b30 571"
  by (oc_eval oc_c30_0571)

lemma oc_c30_0572: "oc_sub oc_b30 572"
  by (oc_eval oc_c30_0572)

lemma oc_c30_0573: "oc_sub oc_b30 573"
  by (oc_eval oc_c30_0573)

lemma oc_c30_0574: "oc_sub oc_b30 574"
  by (oc_eval oc_c30_0574)

lemma oc_c30_0575: "oc_sub oc_b30 575"
  by (oc_eval oc_c30_0575)

lemma upt_c30_035: "[560..<576] = [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]"
  by (simp add: upt_rec)

lemma sec_c30_035: "\<forall>j\<in>{16 * 35..<16 * 35 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 35..<16 * 35 + 16}"
  then have "j \<in> set [560..<576]" unfolding set_upt by simp
  then have "j \<in> set [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]" unfolding upt_c30_035 .
  then show "oc_sub oc_b30 j" using oc_c30_0560 oc_c30_0561 oc_c30_0562 oc_c30_0563 oc_c30_0564 oc_c30_0565 oc_c30_0566 oc_c30_0567 oc_c30_0568 oc_c30_0569 oc_c30_0570 oc_c30_0571 oc_c30_0572 oc_c30_0573 oc_c30_0574 oc_c30_0575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
