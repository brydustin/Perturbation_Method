theory DCX_c30_035
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0560: "dc_sub dc_b30 560"
  by (dc_eval dc_c30_0560)

lemma dc_c30_0561: "dc_sub dc_b30 561"
  by (dc_eval dc_c30_0561)

lemma dc_c30_0562: "dc_sub dc_b30 562"
  by (dc_eval dc_c30_0562)

lemma dc_c30_0563: "dc_sub dc_b30 563"
  by (dc_eval dc_c30_0563)

lemma dc_c30_0564: "dc_sub dc_b30 564"
  by (dc_eval dc_c30_0564)

lemma dc_c30_0565: "dc_sub dc_b30 565"
  by (dc_eval dc_c30_0565)

lemma dc_c30_0566: "dc_sub dc_b30 566"
  by (dc_eval dc_c30_0566)

lemma dc_c30_0567: "dc_sub dc_b30 567"
  by (dc_eval dc_c30_0567)

lemma dc_c30_0568: "dc_sub dc_b30 568"
  by (dc_eval dc_c30_0568)

lemma dc_c30_0569: "dc_sub dc_b30 569"
  by (dc_eval dc_c30_0569)

lemma dc_c30_0570: "dc_sub dc_b30 570"
  by (dc_eval dc_c30_0570)

lemma dc_c30_0571: "dc_sub dc_b30 571"
  by (dc_eval dc_c30_0571)

lemma dc_c30_0572: "dc_sub dc_b30 572"
  by (dc_eval dc_c30_0572)

lemma dc_c30_0573: "dc_sub dc_b30 573"
  by (dc_eval dc_c30_0573)

lemma dc_c30_0574: "dc_sub dc_b30 574"
  by (dc_eval dc_c30_0574)

lemma dc_c30_0575: "dc_sub dc_b30 575"
  by (dc_eval dc_c30_0575)

lemma upt_c30_035: "[560..<576] = [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]"
  by (simp add: upt_rec)

lemma sec_c30_035: "\<forall>j\<in>{16 * 35..<16 * 35 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 35..<16 * 35 + 16}"
  then have "j \<in> set [560..<576]" unfolding set_upt by simp
  then have "j \<in> set [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]" unfolding upt_c30_035 .
  then show "dc_sub dc_b30 j" using dc_c30_0560 dc_c30_0561 dc_c30_0562 dc_c30_0563 dc_c30_0564 dc_c30_0565 dc_c30_0566 dc_c30_0567 dc_c30_0568 dc_c30_0569 dc_c30_0570 dc_c30_0571 dc_c30_0572 dc_c30_0573 dc_c30_0574 dc_c30_0575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
