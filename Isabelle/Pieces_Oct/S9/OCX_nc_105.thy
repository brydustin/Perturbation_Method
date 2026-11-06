theory OCX_nc_105
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1680: "oc_sub None 1680"
  by (oc_eval oc_nc_1680)

lemma oc_nc_1681: "oc_sub None 1681"
  by (oc_eval oc_nc_1681)

lemma oc_nc_1682: "oc_sub None 1682"
  by (oc_eval oc_nc_1682)

lemma oc_nc_1683: "oc_sub None 1683"
  by (oc_eval oc_nc_1683)

lemma oc_nc_1684: "oc_sub None 1684"
  by (oc_eval oc_nc_1684)

lemma oc_nc_1685: "oc_sub None 1685"
  by (oc_eval oc_nc_1685)

lemma oc_nc_1686: "oc_sub None 1686"
  by (oc_eval oc_nc_1686)

lemma oc_nc_1687: "oc_sub None 1687"
  by (oc_eval oc_nc_1687)

lemma oc_nc_1688: "oc_sub None 1688"
  by (oc_eval oc_nc_1688)

lemma oc_nc_1689: "oc_sub None 1689"
  by (oc_eval oc_nc_1689)

lemma oc_nc_1690: "oc_sub None 1690"
  by (oc_eval oc_nc_1690)

lemma oc_nc_1691: "oc_sub None 1691"
  by (oc_eval oc_nc_1691)

lemma oc_nc_1692: "oc_sub None 1692"
  by (oc_eval oc_nc_1692)

lemma oc_nc_1693: "oc_sub None 1693"
  by (oc_eval oc_nc_1693)

lemma oc_nc_1694: "oc_sub None 1694"
  by (oc_eval oc_nc_1694)

lemma oc_nc_1695: "oc_sub None 1695"
  by (oc_eval oc_nc_1695)

lemma upt_nc_105: "[1680..<1696] = [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]"
  by (simp add: upt_rec)

lemma sec_nc_105: "\<forall>j\<in>{16 * 105..<16 * 105 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 105..<16 * 105 + 16}"
  then have "j \<in> set [1680..<1696]" unfolding set_upt by simp
  then have "j \<in> set [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]" unfolding upt_nc_105 .
  then show "oc_sub None j" using oc_nc_1680 oc_nc_1681 oc_nc_1682 oc_nc_1683 oc_nc_1684 oc_nc_1685 oc_nc_1686 oc_nc_1687 oc_nc_1688 oc_nc_1689 oc_nc_1690 oc_nc_1691 oc_nc_1692 oc_nc_1693 oc_nc_1694 oc_nc_1695
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
