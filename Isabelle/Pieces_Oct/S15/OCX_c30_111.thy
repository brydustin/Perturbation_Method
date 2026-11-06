theory OCX_c30_111
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1776: "oc_sub oc_b30 1776"
  by (oc_eval oc_c30_1776)

lemma oc_c30_1777: "oc_sub oc_b30 1777"
  by (oc_eval oc_c30_1777)

lemma oc_c30_1778: "oc_sub oc_b30 1778"
  by (oc_eval oc_c30_1778)

lemma oc_c30_1779: "oc_sub oc_b30 1779"
  by (oc_eval oc_c30_1779)

lemma oc_c30_1780: "oc_sub oc_b30 1780"
  by (oc_eval oc_c30_1780)

lemma oc_c30_1781: "oc_sub oc_b30 1781"
  by (oc_eval oc_c30_1781)

lemma oc_c30_1782: "oc_sub oc_b30 1782"
  by (oc_eval oc_c30_1782)

lemma oc_c30_1783: "oc_sub oc_b30 1783"
  by (oc_eval oc_c30_1783)

lemma oc_c30_1784: "oc_sub oc_b30 1784"
  by (oc_eval oc_c30_1784)

lemma oc_c30_1785: "oc_sub oc_b30 1785"
  by (oc_eval oc_c30_1785)

lemma oc_c30_1786: "oc_sub oc_b30 1786"
  by (oc_eval oc_c30_1786)

lemma oc_c30_1787: "oc_sub oc_b30 1787"
  by (oc_eval oc_c30_1787)

lemma oc_c30_1788: "oc_sub oc_b30 1788"
  by (oc_eval oc_c30_1788)

lemma oc_c30_1789: "oc_sub oc_b30 1789"
  by (oc_eval oc_c30_1789)

lemma oc_c30_1790: "oc_sub oc_b30 1790"
  by (oc_eval oc_c30_1790)

lemma oc_c30_1791: "oc_sub oc_b30 1791"
  by (oc_eval oc_c30_1791)

lemma upt_c30_111: "[1776..<1792] = [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]"
  by (simp add: upt_rec)

lemma sec_c30_111: "\<forall>j\<in>{16 * 111..<16 * 111 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 111..<16 * 111 + 16}"
  then have "j \<in> set [1776..<1792]" unfolding set_upt by simp
  then have "j \<in> set [1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791]" unfolding upt_c30_111 .
  then show "oc_sub oc_b30 j" using oc_c30_1776 oc_c30_1777 oc_c30_1778 oc_c30_1779 oc_c30_1780 oc_c30_1781 oc_c30_1782 oc_c30_1783 oc_c30_1784 oc_c30_1785 oc_c30_1786 oc_c30_1787 oc_c30_1788 oc_c30_1789 oc_c30_1790 oc_c30_1791
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
