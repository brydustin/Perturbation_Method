theory GDCX_nc_110
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1760: "gdc_sub None 1760"
  by (gdc_eval gdc_nc_1760)

lemma gdc_nc_1761: "gdc_sub None 1761"
  by (gdc_eval gdc_nc_1761)

lemma gdc_nc_1762: "gdc_sub None 1762"
  by (gdc_eval gdc_nc_1762)

lemma gdc_nc_1763: "gdc_sub None 1763"
  by (gdc_eval gdc_nc_1763)

lemma gdc_nc_1764: "gdc_sub None 1764"
  by (gdc_eval gdc_nc_1764)

lemma gdc_nc_1765: "gdc_sub None 1765"
  by (gdc_eval gdc_nc_1765)

lemma gdc_nc_1766: "gdc_sub None 1766"
  by (gdc_eval gdc_nc_1766)

lemma gdc_nc_1767: "gdc_sub None 1767"
  by (gdc_eval gdc_nc_1767)

lemma gdc_nc_1768: "gdc_sub None 1768"
  by (gdc_eval gdc_nc_1768)

lemma gdc_nc_1769: "gdc_sub None 1769"
  by (gdc_eval gdc_nc_1769)

lemma gdc_nc_1770: "gdc_sub None 1770"
  by (gdc_eval gdc_nc_1770)

lemma gdc_nc_1771: "gdc_sub None 1771"
  by (gdc_eval gdc_nc_1771)

lemma gdc_nc_1772: "gdc_sub None 1772"
  by (gdc_eval gdc_nc_1772)

lemma gdc_nc_1773: "gdc_sub None 1773"
  by (gdc_eval gdc_nc_1773)

lemma gdc_nc_1774: "gdc_sub None 1774"
  by (gdc_eval gdc_nc_1774)

lemma gdc_nc_1775: "gdc_sub None 1775"
  by (gdc_eval gdc_nc_1775)

lemma gupt_nc_110: "[1760..<1776] = [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]"
  by (simp add: upt_rec)

lemma gsec_nc_110: "\<forall>j\<in>{16 * 110..<16 * 110 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 110..<16 * 110 + 16}"
  then have "j \<in> set [1760..<1776]" unfolding set_upt by simp
  then have "j \<in> set [1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775]" unfolding gupt_nc_110 .
  then show "gdc_sub None j" using gdc_nc_1760 gdc_nc_1761 gdc_nc_1762 gdc_nc_1763 gdc_nc_1764 gdc_nc_1765 gdc_nc_1766 gdc_nc_1767 gdc_nc_1768 gdc_nc_1769 gdc_nc_1770 gdc_nc_1771 gdc_nc_1772 gdc_nc_1773 gdc_nc_1774 gdc_nc_1775
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
