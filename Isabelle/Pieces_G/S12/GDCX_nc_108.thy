theory GDCX_nc_108
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1728: "gdc_sub None 1728"
  by (gdc_eval gdc_nc_1728)

lemma gdc_nc_1729: "gdc_sub None 1729"
  by (gdc_eval gdc_nc_1729)

lemma gdc_nc_1730: "gdc_sub None 1730"
  by (gdc_eval gdc_nc_1730)

lemma gdc_nc_1731: "gdc_sub None 1731"
  by (gdc_eval gdc_nc_1731)

lemma gdc_nc_1732: "gdc_sub None 1732"
  by (gdc_eval gdc_nc_1732)

lemma gdc_nc_1733: "gdc_sub None 1733"
  by (gdc_eval gdc_nc_1733)

lemma gdc_nc_1734: "gdc_sub None 1734"
  by (gdc_eval gdc_nc_1734)

lemma gdc_nc_1735: "gdc_sub None 1735"
  by (gdc_eval gdc_nc_1735)

lemma gdc_nc_1736: "gdc_sub None 1736"
  by (gdc_eval gdc_nc_1736)

lemma gdc_nc_1737: "gdc_sub None 1737"
  by (gdc_eval gdc_nc_1737)

lemma gdc_nc_1738: "gdc_sub None 1738"
  by (gdc_eval gdc_nc_1738)

lemma gdc_nc_1739: "gdc_sub None 1739"
  by (gdc_eval gdc_nc_1739)

lemma gdc_nc_1740: "gdc_sub None 1740"
  by (gdc_eval gdc_nc_1740)

lemma gdc_nc_1741: "gdc_sub None 1741"
  by (gdc_eval gdc_nc_1741)

lemma gdc_nc_1742: "gdc_sub None 1742"
  by (gdc_eval gdc_nc_1742)

lemma gdc_nc_1743: "gdc_sub None 1743"
  by (gdc_eval gdc_nc_1743)

lemma gupt_nc_108: "[1728..<1744] = [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]"
  by (simp add: upt_rec)

lemma gsec_nc_108: "\<forall>j\<in>{16 * 108..<16 * 108 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 108..<16 * 108 + 16}"
  then have "j \<in> set [1728..<1744]" unfolding set_upt by simp
  then have "j \<in> set [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]" unfolding gupt_nc_108 .
  then show "gdc_sub None j" using gdc_nc_1728 gdc_nc_1729 gdc_nc_1730 gdc_nc_1731 gdc_nc_1732 gdc_nc_1733 gdc_nc_1734 gdc_nc_1735 gdc_nc_1736 gdc_nc_1737 gdc_nc_1738 gdc_nc_1739 gdc_nc_1740 gdc_nc_1741 gdc_nc_1742 gdc_nc_1743
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
