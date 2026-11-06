theory DCX_nc_108
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1728: "dc_sub None 1728"
  by (dc_eval dc_nc_1728)

lemma dc_nc_1729: "dc_sub None 1729"
  by (dc_eval dc_nc_1729)

lemma dc_nc_1730: "dc_sub None 1730"
  by (dc_eval dc_nc_1730)

lemma dc_nc_1731: "dc_sub None 1731"
  by (dc_eval dc_nc_1731)

lemma dc_nc_1732: "dc_sub None 1732"
  by (dc_eval dc_nc_1732)

lemma dc_nc_1733: "dc_sub None 1733"
  by (dc_eval dc_nc_1733)

lemma dc_nc_1734: "dc_sub None 1734"
  by (dc_eval dc_nc_1734)

lemma dc_nc_1735: "dc_sub None 1735"
  by (dc_eval dc_nc_1735)

lemma dc_nc_1736: "dc_sub None 1736"
  by (dc_eval dc_nc_1736)

lemma dc_nc_1737: "dc_sub None 1737"
  by (dc_eval dc_nc_1737)

lemma dc_nc_1738: "dc_sub None 1738"
  by (dc_eval dc_nc_1738)

lemma dc_nc_1739: "dc_sub None 1739"
  by (dc_eval dc_nc_1739)

lemma dc_nc_1740: "dc_sub None 1740"
  by (dc_eval dc_nc_1740)

lemma dc_nc_1741: "dc_sub None 1741"
  by (dc_eval dc_nc_1741)

lemma dc_nc_1742: "dc_sub None 1742"
  by (dc_eval dc_nc_1742)

lemma dc_nc_1743: "dc_sub None 1743"
  by (dc_eval dc_nc_1743)

lemma upt_nc_108: "[1728..<1744] = [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]"
  by (simp add: upt_rec)

lemma sec_nc_108: "\<forall>j\<in>{16 * 108..<16 * 108 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 108..<16 * 108 + 16}"
  then have "j \<in> set [1728..<1744]" unfolding set_upt by simp
  then have "j \<in> set [1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743]" unfolding upt_nc_108 .
  then show "dc_sub None j" using dc_nc_1728 dc_nc_1729 dc_nc_1730 dc_nc_1731 dc_nc_1732 dc_nc_1733 dc_nc_1734 dc_nc_1735 dc_nc_1736 dc_nc_1737 dc_nc_1738 dc_nc_1739 dc_nc_1740 dc_nc_1741 dc_nc_1742 dc_nc_1743
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
