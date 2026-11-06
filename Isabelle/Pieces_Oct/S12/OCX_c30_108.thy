theory OCX_c30_108
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1728: "oc_sub oc_b30 1728"
  by (oc_eval oc_c30_1728)

lemma oc_c30_1729: "oc_sub oc_b30 1729"
  by (oc_eval oc_c30_1729)

lemma oc_c30_1730: "oc_sub oc_b30 1730"
  by (oc_eval oc_c30_1730)

lemma oc_c30_1731: "oc_sub oc_b30 1731"
  by (oc_eval oc_c30_1731)

lemma oc_c30_1732: "oc_sub oc_b30 1732"
  by (oc_eval oc_c30_1732)

lemma oc_c30_1733: "oc_sub oc_b30 1733"
  by (oc_eval oc_c30_1733)

lemma oc_c30_1734: "oc_sub oc_b30 1734"
  by (oc_eval oc_c30_1734)

lemma oc_c30_1735: "oc_sub oc_b30 1735"
  by (oc_eval oc_c30_1735)

lemma oc_c30_1736: "oc_sub oc_b30 1736"
  by (oc_eval oc_c30_1736)

lemma oc_c30_1737: "oc_sub oc_b30 1737"
  by (oc_eval oc_c30_1737)

lemma oc_c30_1738: "oc_sub oc_b30 1738"
  by (oc_eval oc_c30_1738)

lemma oc_c30_1739: "oc_sub oc_b30 1739"
  by (oc_eval oc_c30_1739)

lemma oc_c30_1740: "oc_sub oc_b30 1740"
  by (oc_eval oc_c30_1740)

lemma oc_c30_1741: "oc_sub oc_b30 1741"
  by (oc_eval oc_c30_1741)

lemma oc_c30_1742: "oc_sub oc_b30 1742"
  by (oc_eval oc_c30_1742)

lemma oc_c30_1743: "oc_sub oc_b30 1743"
  by (oc_eval oc_c30_1743)

lemma upt_c30_108: "[1728..<1744] = [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]"
  by (simp add: upt_rec)

lemma sec_c30_108: "\<forall>j\<in>{16 * 108..<16 * 108 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 108..<16 * 108 + 16}"
  then have "j \<in> set [1728..<1744]" unfolding set_upt by simp
  then have "j \<in> set [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]" unfolding upt_c30_108 .
  then show "oc_sub oc_b30 j" using oc_c30_1728 oc_c30_1729 oc_c30_1730 oc_c30_1731 oc_c30_1732 oc_c30_1733 oc_c30_1734 oc_c30_1735 oc_c30_1736 oc_c30_1737 oc_c30_1738 oc_c30_1739 oc_c30_1740 oc_c30_1741 oc_c30_1742 oc_c30_1743
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
