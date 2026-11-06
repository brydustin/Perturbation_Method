theory OCX_nc_035
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0560: "oc_sub None 560"
  by (oc_eval oc_nc_0560)

lemma oc_nc_0561: "oc_sub None 561"
  by (oc_eval oc_nc_0561)

lemma oc_nc_0562: "oc_sub None 562"
  by (oc_eval oc_nc_0562)

lemma oc_nc_0563: "oc_sub None 563"
  by (oc_eval oc_nc_0563)

lemma oc_nc_0564: "oc_sub None 564"
  by (oc_eval oc_nc_0564)

lemma oc_nc_0565: "oc_sub None 565"
  by (oc_eval oc_nc_0565)

lemma oc_nc_0566: "oc_sub None 566"
  by (oc_eval oc_nc_0566)

lemma oc_nc_0567: "oc_sub None 567"
  by (oc_eval oc_nc_0567)

lemma oc_nc_0568: "oc_sub None 568"
  by (oc_eval oc_nc_0568)

lemma oc_nc_0569: "oc_sub None 569"
  by (oc_eval oc_nc_0569)

lemma oc_nc_0570: "oc_sub None 570"
  by (oc_eval oc_nc_0570)

lemma oc_nc_0571: "oc_sub None 571"
  by (oc_eval oc_nc_0571)

lemma oc_nc_0572: "oc_sub None 572"
  by (oc_eval oc_nc_0572)

lemma oc_nc_0573: "oc_sub None 573"
  by (oc_eval oc_nc_0573)

lemma oc_nc_0574: "oc_sub None 574"
  by (oc_eval oc_nc_0574)

lemma oc_nc_0575: "oc_sub None 575"
  by (oc_eval oc_nc_0575)

lemma upt_nc_035: "[560..<576] = [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]"
  by (simp add: upt_rec)

lemma sec_nc_035: "\<forall>j\<in>{16 * 35..<16 * 35 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 35..<16 * 35 + 16}"
  then have "j \<in> set [560..<576]" unfolding set_upt by simp
  then have "j \<in> set [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]" unfolding upt_nc_035 .
  then show "oc_sub None j" using oc_nc_0560 oc_nc_0561 oc_nc_0562 oc_nc_0563 oc_nc_0564 oc_nc_0565 oc_nc_0566 oc_nc_0567 oc_nc_0568 oc_nc_0569 oc_nc_0570 oc_nc_0571 oc_nc_0572 oc_nc_0573 oc_nc_0574 oc_nc_0575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
