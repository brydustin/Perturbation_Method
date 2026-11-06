theory OCX_c30_110
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1760: "oc_sub oc_b30 1760"
  by (oc_eval oc_c30_1760)

lemma oc_c30_1761: "oc_sub oc_b30 1761"
  by (oc_eval oc_c30_1761)

lemma oc_c30_1762: "oc_sub oc_b30 1762"
  by (oc_eval oc_c30_1762)

lemma oc_c30_1763: "oc_sub oc_b30 1763"
  by (oc_eval oc_c30_1763)

lemma oc_c30_1764: "oc_sub oc_b30 1764"
  by (oc_eval oc_c30_1764)

lemma oc_c30_1765: "oc_sub oc_b30 1765"
  by (oc_eval oc_c30_1765)

lemma oc_c30_1766: "oc_sub oc_b30 1766"
  by (oc_eval oc_c30_1766)

lemma oc_c30_1767: "oc_sub oc_b30 1767"
  by (oc_eval oc_c30_1767)

lemma oc_c30_1768: "oc_sub oc_b30 1768"
  by (oc_eval oc_c30_1768)

lemma oc_c30_1769: "oc_sub oc_b30 1769"
  by (oc_eval oc_c30_1769)

lemma oc_c30_1770: "oc_sub oc_b30 1770"
  by (oc_eval oc_c30_1770)

lemma oc_c30_1771: "oc_sub oc_b30 1771"
  by (oc_eval oc_c30_1771)

lemma oc_c30_1772: "oc_sub oc_b30 1772"
  by (oc_eval oc_c30_1772)

lemma oc_c30_1773: "oc_sub oc_b30 1773"
  by (oc_eval oc_c30_1773)

lemma oc_c30_1774: "oc_sub oc_b30 1774"
  by (oc_eval oc_c30_1774)

lemma oc_c30_1775: "oc_sub oc_b30 1775"
  by (oc_eval oc_c30_1775)

lemma upt_c30_110: "[1760..<1776] = [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]"
  by (simp add: upt_rec)

lemma sec_c30_110: "\<forall>j\<in>{16 * 110..<16 * 110 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 110..<16 * 110 + 16}"
  then have "j \<in> set [1760..<1776]" unfolding set_upt by simp
  then have "j \<in> set [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]" unfolding upt_c30_110 .
  then show "oc_sub oc_b30 j" using oc_c30_1760 oc_c30_1761 oc_c30_1762 oc_c30_1763 oc_c30_1764 oc_c30_1765 oc_c30_1766 oc_c30_1767 oc_c30_1768 oc_c30_1769 oc_c30_1770 oc_c30_1771 oc_c30_1772 oc_c30_1773 oc_c30_1774 oc_c30_1775
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
