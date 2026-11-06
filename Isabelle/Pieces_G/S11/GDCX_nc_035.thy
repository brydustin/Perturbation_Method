theory GDCX_nc_035
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0560: "gdc_sub None 560"
  by (gdc_eval gdc_nc_0560)

lemma gdc_nc_0561: "gdc_sub None 561"
  by (gdc_eval gdc_nc_0561)

lemma gdc_nc_0562: "gdc_sub None 562"
  by (gdc_eval gdc_nc_0562)

lemma gdc_nc_0563: "gdc_sub None 563"
  by (gdc_eval gdc_nc_0563)

lemma gdc_nc_0564: "gdc_sub None 564"
  by (gdc_eval gdc_nc_0564)

lemma gdc_nc_0565: "gdc_sub None 565"
  by (gdc_eval gdc_nc_0565)

lemma gdc_nc_0566: "gdc_sub None 566"
  by (gdc_eval gdc_nc_0566)

lemma gdc_nc_0567: "gdc_sub None 567"
  by (gdc_eval gdc_nc_0567)

lemma gdc_nc_0568: "gdc_sub None 568"
  by (gdc_eval gdc_nc_0568)

lemma gdc_nc_0569: "gdc_sub None 569"
  by (gdc_eval gdc_nc_0569)

lemma gdc_nc_0570: "gdc_sub None 570"
  by (gdc_eval gdc_nc_0570)

lemma gdc_nc_0571: "gdc_sub None 571"
  by (gdc_eval gdc_nc_0571)

lemma gdc_nc_0572: "gdc_sub None 572"
  by (gdc_eval gdc_nc_0572)

lemma gdc_nc_0573: "gdc_sub None 573"
  by (gdc_eval gdc_nc_0573)

lemma gdc_nc_0574: "gdc_sub None 574"
  by (gdc_eval gdc_nc_0574)

lemma gdc_nc_0575: "gdc_sub None 575"
  by (gdc_eval gdc_nc_0575)

lemma gupt_nc_035: "[560..<576] = [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]"
  by (simp add: upt_rec)

lemma gsec_nc_035: "\<forall>j\<in>{16 * 35..<16 * 35 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 35..<16 * 35 + 16}"
  then have "j \<in> set [560..<576]" unfolding set_upt by simp
  then have "j \<in> set [560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575]" unfolding gupt_nc_035 .
  then show "gdc_sub None j" using gdc_nc_0560 gdc_nc_0561 gdc_nc_0562 gdc_nc_0563 gdc_nc_0564 gdc_nc_0565 gdc_nc_0566 gdc_nc_0567 gdc_nc_0568 gdc_nc_0569 gdc_nc_0570 gdc_nc_0571 gdc_nc_0572 gdc_nc_0573 gdc_nc_0574 gdc_nc_0575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
