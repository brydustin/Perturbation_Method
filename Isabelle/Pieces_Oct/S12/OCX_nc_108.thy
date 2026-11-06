theory OCX_nc_108
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1728: "oc_sub None 1728"
  by (oc_eval oc_nc_1728)

lemma oc_nc_1729: "oc_sub None 1729"
  by (oc_eval oc_nc_1729)

lemma oc_nc_1730: "oc_sub None 1730"
  by (oc_eval oc_nc_1730)

lemma oc_nc_1731: "oc_sub None 1731"
  by (oc_eval oc_nc_1731)

lemma oc_nc_1732: "oc_sub None 1732"
  by (oc_eval oc_nc_1732)

lemma oc_nc_1733: "oc_sub None 1733"
  by (oc_eval oc_nc_1733)

lemma oc_nc_1734: "oc_sub None 1734"
  by (oc_eval oc_nc_1734)

lemma oc_nc_1735: "oc_sub None 1735"
  by (oc_eval oc_nc_1735)

lemma oc_nc_1736: "oc_sub None 1736"
  by (oc_eval oc_nc_1736)

lemma oc_nc_1737: "oc_sub None 1737"
  by (oc_eval oc_nc_1737)

lemma oc_nc_1738: "oc_sub None 1738"
  by (oc_eval oc_nc_1738)

lemma oc_nc_1739: "oc_sub None 1739"
  by (oc_eval oc_nc_1739)

lemma oc_nc_1740: "oc_sub None 1740"
  by (oc_eval oc_nc_1740)

lemma oc_nc_1741: "oc_sub None 1741"
  by (oc_eval oc_nc_1741)

lemma oc_nc_1742: "oc_sub None 1742"
  by (oc_eval oc_nc_1742)

lemma oc_nc_1743: "oc_sub None 1743"
  by (oc_eval oc_nc_1743)

lemma upt_nc_108: "[1728..<1744] = [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]"
  by (simp add: upt_rec)

lemma sec_nc_108: "\<forall>j\<in>{16 * 108..<16 * 108 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 108..<16 * 108 + 16}"
  then have "j \<in> set [1728..<1744]" unfolding set_upt by simp
  then have "j \<in> set [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]" unfolding upt_nc_108 .
  then show "oc_sub None j" using oc_nc_1728 oc_nc_1729 oc_nc_1730 oc_nc_1731 oc_nc_1732 oc_nc_1733 oc_nc_1734 oc_nc_1735 oc_nc_1736 oc_nc_1737 oc_nc_1738 oc_nc_1739 oc_nc_1740 oc_nc_1741 oc_nc_1742 oc_nc_1743
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
