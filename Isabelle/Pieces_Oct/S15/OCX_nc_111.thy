theory OCX_nc_111
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1776: "oc_sub None 1776"
  by (oc_eval oc_nc_1776)

lemma oc_nc_1777: "oc_sub None 1777"
  by (oc_eval oc_nc_1777)

lemma oc_nc_1778: "oc_sub None 1778"
  by (oc_eval oc_nc_1778)

lemma oc_nc_1779: "oc_sub None 1779"
  by (oc_eval oc_nc_1779)

lemma oc_nc_1780: "oc_sub None 1780"
  by (oc_eval oc_nc_1780)

lemma oc_nc_1781: "oc_sub None 1781"
  by (oc_eval oc_nc_1781)

lemma oc_nc_1782: "oc_sub None 1782"
  by (oc_eval oc_nc_1782)

lemma oc_nc_1783: "oc_sub None 1783"
  by (oc_eval oc_nc_1783)

lemma oc_nc_1784: "oc_sub None 1784"
  by (oc_eval oc_nc_1784)

lemma oc_nc_1785: "oc_sub None 1785"
  by (oc_eval oc_nc_1785)

lemma oc_nc_1786: "oc_sub None 1786"
  by (oc_eval oc_nc_1786)

lemma oc_nc_1787: "oc_sub None 1787"
  by (oc_eval oc_nc_1787)

lemma oc_nc_1788: "oc_sub None 1788"
  by (oc_eval oc_nc_1788)

lemma oc_nc_1789: "oc_sub None 1789"
  by (oc_eval oc_nc_1789)

lemma oc_nc_1790: "oc_sub None 1790"
  by (oc_eval oc_nc_1790)

lemma oc_nc_1791: "oc_sub None 1791"
  by (oc_eval oc_nc_1791)

lemma upt_nc_111: "[1776..<1792] = [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]"
  by (simp add: upt_rec)

lemma sec_nc_111: "\<forall>j\<in>{16 * 111..<16 * 111 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 111..<16 * 111 + 16}"
  then have "j \<in> set [1776..<1792]" unfolding set_upt by simp
  then have "j \<in> set [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]" unfolding upt_nc_111 .
  then show "oc_sub None j" using oc_nc_1776 oc_nc_1777 oc_nc_1778 oc_nc_1779 oc_nc_1780 oc_nc_1781 oc_nc_1782 oc_nc_1783 oc_nc_1784 oc_nc_1785 oc_nc_1786 oc_nc_1787 oc_nc_1788 oc_nc_1789 oc_nc_1790 oc_nc_1791
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
