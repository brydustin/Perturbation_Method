theory DCX_c30_108
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1728: "dc_sub dc_b30 1728"
  by (dc_eval dc_c30_1728)

lemma dc_c30_1729: "dc_sub dc_b30 1729"
  by (dc_eval dc_c30_1729)

lemma dc_c30_1730: "dc_sub dc_b30 1730"
  by (dc_eval dc_c30_1730)

lemma dc_c30_1731: "dc_sub dc_b30 1731"
  by (dc_eval dc_c30_1731)

lemma dc_c30_1732: "dc_sub dc_b30 1732"
  by (dc_eval dc_c30_1732)

lemma dc_c30_1733: "dc_sub dc_b30 1733"
  by (dc_eval dc_c30_1733)

lemma dc_c30_1734: "dc_sub dc_b30 1734"
  by (dc_eval dc_c30_1734)

lemma dc_c30_1735: "dc_sub dc_b30 1735"
  by (dc_eval dc_c30_1735)

lemma dc_c30_1736: "dc_sub dc_b30 1736"
  by (dc_eval dc_c30_1736)

lemma dc_c30_1737: "dc_sub dc_b30 1737"
  by (dc_eval dc_c30_1737)

lemma dc_c30_1738: "dc_sub dc_b30 1738"
  by (dc_eval dc_c30_1738)

lemma dc_c30_1739: "dc_sub dc_b30 1739"
  by (dc_eval dc_c30_1739)

lemma dc_c30_1740: "dc_sub dc_b30 1740"
  by (dc_eval dc_c30_1740)

lemma dc_c30_1741: "dc_sub dc_b30 1741"
  by (dc_eval dc_c30_1741)

lemma dc_c30_1742: "dc_sub dc_b30 1742"
  by (dc_eval dc_c30_1742)

lemma dc_c30_1743: "dc_sub dc_b30 1743"
  by (dc_eval dc_c30_1743)

lemma upt_c30_108: "[1728..<1744] = [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]"
  by (simp add: upt_rec)

lemma sec_c30_108: "\<forall>j\<in>{16 * 108..<16 * 108 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 108..<16 * 108 + 16}"
  then have "j \<in> set [1728..<1744]" unfolding set_upt by simp
  then have "j \<in> set [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]" unfolding upt_c30_108 .
  then show "dc_sub dc_b30 j" using dc_c30_1728 dc_c30_1729 dc_c30_1730 dc_c30_1731 dc_c30_1732 dc_c30_1733 dc_c30_1734 dc_c30_1735 dc_c30_1736 dc_c30_1737 dc_c30_1738 dc_c30_1739 dc_c30_1740 dc_c30_1741 dc_c30_1742 dc_c30_1743
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
