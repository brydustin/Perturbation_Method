theory DCX_c30_110
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1760: "dc_sub dc_b30 1760"
  by (dc_eval dc_c30_1760)

lemma dc_c30_1761: "dc_sub dc_b30 1761"
  by (dc_eval dc_c30_1761)

lemma dc_c30_1762: "dc_sub dc_b30 1762"
  by (dc_eval dc_c30_1762)

lemma dc_c30_1763: "dc_sub dc_b30 1763"
  by (dc_eval dc_c30_1763)

lemma dc_c30_1764: "dc_sub dc_b30 1764"
  by (dc_eval dc_c30_1764)

lemma dc_c30_1765: "dc_sub dc_b30 1765"
  by (dc_eval dc_c30_1765)

lemma dc_c30_1766: "dc_sub dc_b30 1766"
  by (dc_eval dc_c30_1766)

lemma dc_c30_1767: "dc_sub dc_b30 1767"
  by (dc_eval dc_c30_1767)

lemma dc_c30_1768: "dc_sub dc_b30 1768"
  by (dc_eval dc_c30_1768)

lemma dc_c30_1769: "dc_sub dc_b30 1769"
  by (dc_eval dc_c30_1769)

lemma dc_c30_1770: "dc_sub dc_b30 1770"
  by (dc_eval dc_c30_1770)

lemma dc_c30_1771: "dc_sub dc_b30 1771"
  by (dc_eval dc_c30_1771)

lemma dc_c30_1772: "dc_sub dc_b30 1772"
  by (dc_eval dc_c30_1772)

lemma dc_c30_1773: "dc_sub dc_b30 1773"
  by (dc_eval dc_c30_1773)

lemma dc_c30_1774: "dc_sub dc_b30 1774"
  by (dc_eval dc_c30_1774)

lemma dc_c30_1775: "dc_sub dc_b30 1775"
  by (dc_eval dc_c30_1775)

lemma upt_c30_110: "[1760..<1776] = [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]"
  by (simp add: upt_rec)

lemma sec_c30_110: "\<forall>j\<in>{16 * 110..<16 * 110 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 110..<16 * 110 + 16}"
  then have "j \<in> set [1760..<1776]" unfolding set_upt by simp
  then have "j \<in> set [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]" unfolding upt_c30_110 .
  then show "dc_sub dc_b30 j" using dc_c30_1760 dc_c30_1761 dc_c30_1762 dc_c30_1763 dc_c30_1764 dc_c30_1765 dc_c30_1766 dc_c30_1767 dc_c30_1768 dc_c30_1769 dc_c30_1770 dc_c30_1771 dc_c30_1772 dc_c30_1773 dc_c30_1774 dc_c30_1775
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
