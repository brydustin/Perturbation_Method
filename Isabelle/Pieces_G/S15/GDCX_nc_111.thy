theory GDCX_nc_111
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1776: "gdc_sub None 1776"
  by (gdc_eval gdc_nc_1776)

lemma gdc_nc_1777: "gdc_sub None 1777"
  by (gdc_eval gdc_nc_1777)

lemma gdc_nc_1778: "gdc_sub None 1778"
  by (gdc_eval gdc_nc_1778)

lemma gdc_nc_1779: "gdc_sub None 1779"
  by (gdc_eval gdc_nc_1779)

lemma gdc_nc_1780: "gdc_sub None 1780"
  by (gdc_eval gdc_nc_1780)

lemma gdc_nc_1781: "gdc_sub None 1781"
  by (gdc_eval gdc_nc_1781)

lemma gdc_nc_1782: "gdc_sub None 1782"
  by (gdc_eval gdc_nc_1782)

lemma gdc_nc_1783: "gdc_sub None 1783"
  by (gdc_eval gdc_nc_1783)

lemma gdc_nc_1784: "gdc_sub None 1784"
  by (gdc_eval gdc_nc_1784)

lemma gdc_nc_1785: "gdc_sub None 1785"
  by (gdc_eval gdc_nc_1785)

lemma gdc_nc_1786: "gdc_sub None 1786"
  by (gdc_eval gdc_nc_1786)

lemma gdc_nc_1787: "gdc_sub None 1787"
  by (gdc_eval gdc_nc_1787)

lemma gdc_nc_1788: "gdc_sub None 1788"
  by (gdc_eval gdc_nc_1788)

lemma gdc_nc_1789: "gdc_sub None 1789"
  by (gdc_eval gdc_nc_1789)

lemma gdc_nc_1790: "gdc_sub None 1790"
  by (gdc_eval gdc_nc_1790)

lemma gdc_nc_1791: "gdc_sub None 1791"
  by (gdc_eval gdc_nc_1791)

lemma gupt_nc_111: "[1776..<1792] = [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]"
  by (simp add: upt_rec)

lemma gsec_nc_111: "\<forall>j\<in>{16 * 111..<16 * 111 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 111..<16 * 111 + 16}"
  then have "j \<in> set [1776..<1792]" unfolding set_upt by simp
  then have "j \<in> set [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]" unfolding gupt_nc_111 .
  then show "gdc_sub None j" using gdc_nc_1776 gdc_nc_1777 gdc_nc_1778 gdc_nc_1779 gdc_nc_1780 gdc_nc_1781 gdc_nc_1782 gdc_nc_1783 gdc_nc_1784 gdc_nc_1785 gdc_nc_1786 gdc_nc_1787 gdc_nc_1788 gdc_nc_1789 gdc_nc_1790 gdc_nc_1791
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
