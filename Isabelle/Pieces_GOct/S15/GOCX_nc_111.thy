theory GOCX_nc_111
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1776: "goc_sub None 1776"
  by (goc_eval goc_nc_1776)

lemma goc_nc_1777: "goc_sub None 1777"
  by (goc_eval goc_nc_1777)

lemma goc_nc_1778: "goc_sub None 1778"
  by (goc_eval goc_nc_1778)

lemma goc_nc_1779: "goc_sub None 1779"
  by (goc_eval goc_nc_1779)

lemma goc_nc_1780: "goc_sub None 1780"
  by (goc_eval goc_nc_1780)

lemma goc_nc_1781: "goc_sub None 1781"
  by (goc_eval goc_nc_1781)

lemma goc_nc_1782: "goc_sub None 1782"
  by (goc_eval goc_nc_1782)

lemma goc_nc_1783: "goc_sub None 1783"
  by (goc_eval goc_nc_1783)

lemma goc_nc_1784: "goc_sub None 1784"
  by (goc_eval goc_nc_1784)

lemma goc_nc_1785: "goc_sub None 1785"
  by (goc_eval goc_nc_1785)

lemma goc_nc_1786: "goc_sub None 1786"
  by (goc_eval goc_nc_1786)

lemma goc_nc_1787: "goc_sub None 1787"
  by (goc_eval goc_nc_1787)

lemma goc_nc_1788: "goc_sub None 1788"
  by (goc_eval goc_nc_1788)

lemma goc_nc_1789: "goc_sub None 1789"
  by (goc_eval goc_nc_1789)

lemma goc_nc_1790: "goc_sub None 1790"
  by (goc_eval goc_nc_1790)

lemma goc_nc_1791: "goc_sub None 1791"
  by (goc_eval goc_nc_1791)

lemma gupt_nc_111: "[1776..<1792] = [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]"
  by (simp add: upt_rec)

lemma gsec_nc_111: "\<forall>j\<in>{16 * 111..<16 * 111 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 111..<16 * 111 + 16}"
  then have "j \<in> set [1776..<1792]" unfolding set_upt by simp
  then have "j \<in> set [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]" unfolding gupt_nc_111 .
  then show "goc_sub None j" using goc_nc_1776 goc_nc_1777 goc_nc_1778 goc_nc_1779 goc_nc_1780 goc_nc_1781 goc_nc_1782 goc_nc_1783 goc_nc_1784 goc_nc_1785 goc_nc_1786 goc_nc_1787 goc_nc_1788 goc_nc_1789 goc_nc_1790 goc_nc_1791
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
