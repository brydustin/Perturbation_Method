theory GOCX_nc_035
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0560: "goc_sub None 560"
  by (goc_eval goc_nc_0560)

lemma goc_nc_0561: "goc_sub None 561"
  by (goc_eval goc_nc_0561)

lemma goc_nc_0562: "goc_sub None 562"
  by (goc_eval goc_nc_0562)

lemma goc_nc_0563: "goc_sub None 563"
  by (goc_eval goc_nc_0563)

lemma goc_nc_0564: "goc_sub None 564"
  by (goc_eval goc_nc_0564)

lemma goc_nc_0565: "goc_sub None 565"
  by (goc_eval goc_nc_0565)

lemma goc_nc_0566: "goc_sub None 566"
  by (goc_eval goc_nc_0566)

lemma goc_nc_0567: "goc_sub None 567"
  by (goc_eval goc_nc_0567)

lemma goc_nc_0568: "goc_sub None 568"
  by (goc_eval goc_nc_0568)

lemma goc_nc_0569: "goc_sub None 569"
  by (goc_eval goc_nc_0569)

lemma goc_nc_0570: "goc_sub None 570"
  by (goc_eval goc_nc_0570)

lemma goc_nc_0571: "goc_sub None 571"
  by (goc_eval goc_nc_0571)

lemma goc_nc_0572: "goc_sub None 572"
  by (goc_eval goc_nc_0572)

lemma goc_nc_0573: "goc_sub None 573"
  by (goc_eval goc_nc_0573)

lemma goc_nc_0574: "goc_sub None 574"
  by (goc_eval goc_nc_0574)

lemma goc_nc_0575: "goc_sub None 575"
  by (goc_eval goc_nc_0575)

lemma gupt_nc_035: "[560..<576] = [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]"
  by (simp add: upt_rec)

lemma gsec_nc_035: "\<forall>j\<in>{16 * 35..<16 * 35 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 35..<16 * 35 + 16}"
  then have "j \<in> set [560..<576]" unfolding set_upt by simp
  then have "j \<in> set [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]" unfolding gupt_nc_035 .
  then show "goc_sub None j" using goc_nc_0560 goc_nc_0561 goc_nc_0562 goc_nc_0563 goc_nc_0564 goc_nc_0565 goc_nc_0566 goc_nc_0567 goc_nc_0568 goc_nc_0569 goc_nc_0570 goc_nc_0571 goc_nc_0572 goc_nc_0573 goc_nc_0574 goc_nc_0575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
