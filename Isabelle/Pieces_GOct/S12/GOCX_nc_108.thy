theory GOCX_nc_108
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1728: "goc_sub None 1728"
  by (goc_eval goc_nc_1728)

lemma goc_nc_1729: "goc_sub None 1729"
  by (goc_eval goc_nc_1729)

lemma goc_nc_1730: "goc_sub None 1730"
  by (goc_eval goc_nc_1730)

lemma goc_nc_1731: "goc_sub None 1731"
  by (goc_eval goc_nc_1731)

lemma goc_nc_1732: "goc_sub None 1732"
  by (goc_eval goc_nc_1732)

lemma goc_nc_1733: "goc_sub None 1733"
  by (goc_eval goc_nc_1733)

lemma goc_nc_1734: "goc_sub None 1734"
  by (goc_eval goc_nc_1734)

lemma goc_nc_1735: "goc_sub None 1735"
  by (goc_eval goc_nc_1735)

lemma goc_nc_1736: "goc_sub None 1736"
  by (goc_eval goc_nc_1736)

lemma goc_nc_1737: "goc_sub None 1737"
  by (goc_eval goc_nc_1737)

lemma goc_nc_1738: "goc_sub None 1738"
  by (goc_eval goc_nc_1738)

lemma goc_nc_1739: "goc_sub None 1739"
  by (goc_eval goc_nc_1739)

lemma goc_nc_1740: "goc_sub None 1740"
  by (goc_eval goc_nc_1740)

lemma goc_nc_1741: "goc_sub None 1741"
  by (goc_eval goc_nc_1741)

lemma goc_nc_1742: "goc_sub None 1742"
  by (goc_eval goc_nc_1742)

lemma goc_nc_1743: "goc_sub None 1743"
  by (goc_eval goc_nc_1743)

lemma gupt_nc_108: "[1728..<1744] = [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]"
  by (simp add: upt_rec)

lemma gsec_nc_108: "\<forall>j\<in>{16 * 108..<16 * 108 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 108..<16 * 108 + 16}"
  then have "j \<in> set [1728..<1744]" unfolding set_upt by simp
  then have "j \<in> set [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]" unfolding gupt_nc_108 .
  then show "goc_sub None j" using goc_nc_1728 goc_nc_1729 goc_nc_1730 goc_nc_1731 goc_nc_1732 goc_nc_1733 goc_nc_1734 goc_nc_1735 goc_nc_1736 goc_nc_1737 goc_nc_1738 goc_nc_1739 goc_nc_1740 goc_nc_1741 goc_nc_1742 goc_nc_1743
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
