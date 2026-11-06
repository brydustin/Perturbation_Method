theory GOCX_nc_110
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1760: "goc_sub None 1760"
  by (goc_eval goc_nc_1760)

lemma goc_nc_1761: "goc_sub None 1761"
  by (goc_eval goc_nc_1761)

lemma goc_nc_1762: "goc_sub None 1762"
  by (goc_eval goc_nc_1762)

lemma goc_nc_1763: "goc_sub None 1763"
  by (goc_eval goc_nc_1763)

lemma goc_nc_1764: "goc_sub None 1764"
  by (goc_eval goc_nc_1764)

lemma goc_nc_1765: "goc_sub None 1765"
  by (goc_eval goc_nc_1765)

lemma goc_nc_1766: "goc_sub None 1766"
  by (goc_eval goc_nc_1766)

lemma goc_nc_1767: "goc_sub None 1767"
  by (goc_eval goc_nc_1767)

lemma goc_nc_1768: "goc_sub None 1768"
  by (goc_eval goc_nc_1768)

lemma goc_nc_1769: "goc_sub None 1769"
  by (goc_eval goc_nc_1769)

lemma goc_nc_1770: "goc_sub None 1770"
  by (goc_eval goc_nc_1770)

lemma goc_nc_1771: "goc_sub None 1771"
  by (goc_eval goc_nc_1771)

lemma goc_nc_1772: "goc_sub None 1772"
  by (goc_eval goc_nc_1772)

lemma goc_nc_1773: "goc_sub None 1773"
  by (goc_eval goc_nc_1773)

lemma goc_nc_1774: "goc_sub None 1774"
  by (goc_eval goc_nc_1774)

lemma goc_nc_1775: "goc_sub None 1775"
  by (goc_eval goc_nc_1775)

lemma gupt_nc_110: "[1760..<1776] = [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]"
  by (simp add: upt_rec)

lemma gsec_nc_110: "\<forall>j\<in>{16 * 110..<16 * 110 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 110..<16 * 110 + 16}"
  then have "j \<in> set [1760..<1776]" unfolding set_upt by simp
  then have "j \<in> set [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]" unfolding gupt_nc_110 .
  then show "goc_sub None j" using goc_nc_1760 goc_nc_1761 goc_nc_1762 goc_nc_1763 goc_nc_1764 goc_nc_1765 goc_nc_1766 goc_nc_1767 goc_nc_1768 goc_nc_1769 goc_nc_1770 goc_nc_1771 goc_nc_1772 goc_nc_1773 goc_nc_1774 goc_nc_1775
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
