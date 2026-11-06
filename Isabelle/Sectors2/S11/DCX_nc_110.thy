theory DCX_nc_110
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1760: "dc_sub None 1760"
  by (dc_eval dc_nc_1760)

lemma dc_nc_1761: "dc_sub None 1761"
  by (dc_eval dc_nc_1761)

lemma dc_nc_1762: "dc_sub None 1762"
  by (dc_eval dc_nc_1762)

lemma dc_nc_1763: "dc_sub None 1763"
  by (dc_eval dc_nc_1763)

lemma dc_nc_1764: "dc_sub None 1764"
  by (dc_eval dc_nc_1764)

lemma dc_nc_1765: "dc_sub None 1765"
  by (dc_eval dc_nc_1765)

lemma dc_nc_1766: "dc_sub None 1766"
  by (dc_eval dc_nc_1766)

lemma dc_nc_1767: "dc_sub None 1767"
  by (dc_eval dc_nc_1767)

lemma dc_nc_1768: "dc_sub None 1768"
  by (dc_eval dc_nc_1768)

lemma dc_nc_1769: "dc_sub None 1769"
  by (dc_eval dc_nc_1769)

lemma dc_nc_1770: "dc_sub None 1770"
  by (dc_eval dc_nc_1770)

lemma dc_nc_1771: "dc_sub None 1771"
  by (dc_eval dc_nc_1771)

lemma dc_nc_1772: "dc_sub None 1772"
  by (dc_eval dc_nc_1772)

lemma dc_nc_1773: "dc_sub None 1773"
  by (dc_eval dc_nc_1773)

lemma dc_nc_1774: "dc_sub None 1774"
  by (dc_eval dc_nc_1774)

lemma dc_nc_1775: "dc_sub None 1775"
  by (dc_eval dc_nc_1775)

lemma upt_nc_110: "[1760..<1776] = [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]"
  by (simp add: upt_rec)

lemma sec_nc_110: "\<forall>j\<in>{16 * 110..<16 * 110 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 110..<16 * 110 + 16}"
  then have "j \<in> set [1760..<1776]" unfolding set_upt by simp
  then have "j \<in> set [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]" unfolding upt_nc_110 .
  then show "dc_sub None j" using dc_nc_1760 dc_nc_1761 dc_nc_1762 dc_nc_1763 dc_nc_1764 dc_nc_1765 dc_nc_1766 dc_nc_1767 dc_nc_1768 dc_nc_1769 dc_nc_1770 dc_nc_1771 dc_nc_1772 dc_nc_1773 dc_nc_1774 dc_nc_1775
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
