theory DCX_nc_111
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1776: "dc_sub None 1776"
  by (dc_eval dc_nc_1776)

lemma dc_nc_1777: "dc_sub None 1777"
  by (dc_eval dc_nc_1777)

lemma dc_nc_1778: "dc_sub None 1778"
  by (dc_eval dc_nc_1778)

lemma dc_nc_1779: "dc_sub None 1779"
  by (dc_eval dc_nc_1779)

lemma dc_nc_1780: "dc_sub None 1780"
  by (dc_eval dc_nc_1780)

lemma dc_nc_1781: "dc_sub None 1781"
  by (dc_eval dc_nc_1781)

lemma dc_nc_1782: "dc_sub None 1782"
  by (dc_eval dc_nc_1782)

lemma dc_nc_1783: "dc_sub None 1783"
  by (dc_eval dc_nc_1783)

lemma dc_nc_1784: "dc_sub None 1784"
  by (dc_eval dc_nc_1784)

lemma dc_nc_1785: "dc_sub None 1785"
  by (dc_eval dc_nc_1785)

lemma dc_nc_1786: "dc_sub None 1786"
  by (dc_eval dc_nc_1786)

lemma dc_nc_1787: "dc_sub None 1787"
  by (dc_eval dc_nc_1787)

lemma dc_nc_1788: "dc_sub None 1788"
  by (dc_eval dc_nc_1788)

lemma dc_nc_1789: "dc_sub None 1789"
  by (dc_eval dc_nc_1789)

lemma dc_nc_1790: "dc_sub None 1790"
  by (dc_eval dc_nc_1790)

lemma dc_nc_1791: "dc_sub None 1791"
  by (dc_eval dc_nc_1791)

lemma upt_nc_111: "[1776..<1792] = [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]"
  by (simp add: upt_rec)

lemma sec_nc_111: "\<forall>j\<in>{16 * 111..<16 * 111 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 111..<16 * 111 + 16}"
  then have "j \<in> set [1776..<1792]" unfolding set_upt by simp
  then have "j \<in> set [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]" unfolding upt_nc_111 .
  then show "dc_sub None j" using dc_nc_1776 dc_nc_1777 dc_nc_1778 dc_nc_1779 dc_nc_1780 dc_nc_1781 dc_nc_1782 dc_nc_1783 dc_nc_1784 dc_nc_1785 dc_nc_1786 dc_nc_1787 dc_nc_1788 dc_nc_1789 dc_nc_1790 dc_nc_1791
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
