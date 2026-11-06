theory OCX_nc_110
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1760: "oc_sub None 1760"
  by (oc_eval oc_nc_1760)

lemma oc_nc_1761: "oc_sub None 1761"
  by (oc_eval oc_nc_1761)

lemma oc_nc_1762: "oc_sub None 1762"
  by (oc_eval oc_nc_1762)

lemma oc_nc_1763: "oc_sub None 1763"
  by (oc_eval oc_nc_1763)

lemma oc_nc_1764: "oc_sub None 1764"
  by (oc_eval oc_nc_1764)

lemma oc_nc_1765: "oc_sub None 1765"
  by (oc_eval oc_nc_1765)

lemma oc_nc_1766: "oc_sub None 1766"
  by (oc_eval oc_nc_1766)

lemma oc_nc_1767: "oc_sub None 1767"
  by (oc_eval oc_nc_1767)

lemma oc_nc_1768: "oc_sub None 1768"
  by (oc_eval oc_nc_1768)

lemma oc_nc_1769: "oc_sub None 1769"
  by (oc_eval oc_nc_1769)

lemma oc_nc_1770: "oc_sub None 1770"
  by (oc_eval oc_nc_1770)

lemma oc_nc_1771: "oc_sub None 1771"
  by (oc_eval oc_nc_1771)

lemma oc_nc_1772: "oc_sub None 1772"
  by (oc_eval oc_nc_1772)

lemma oc_nc_1773: "oc_sub None 1773"
  by (oc_eval oc_nc_1773)

lemma oc_nc_1774: "oc_sub None 1774"
  by (oc_eval oc_nc_1774)

lemma oc_nc_1775: "oc_sub None 1775"
  by (oc_eval oc_nc_1775)

lemma upt_nc_110: "[1760..<1776] = [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]"
  by (simp add: upt_rec)

lemma sec_nc_110: "\<forall>j\<in>{16 * 110..<16 * 110 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 110..<16 * 110 + 16}"
  then have "j \<in> set [1760..<1776]" unfolding set_upt by simp
  then have "j \<in> set [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]" unfolding upt_nc_110 .
  then show "oc_sub None j" using oc_nc_1760 oc_nc_1761 oc_nc_1762 oc_nc_1763 oc_nc_1764 oc_nc_1765 oc_nc_1766 oc_nc_1767 oc_nc_1768 oc_nc_1769 oc_nc_1770 oc_nc_1771 oc_nc_1772 oc_nc_1773 oc_nc_1774 oc_nc_1775
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
