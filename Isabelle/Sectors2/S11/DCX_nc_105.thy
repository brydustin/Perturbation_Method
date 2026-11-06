theory DCX_nc_105
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1680: "dc_sub None 1680"
  by (dc_eval dc_nc_1680)

lemma dc_nc_1681: "dc_sub None 1681"
  by (dc_eval dc_nc_1681)

lemma dc_nc_1682: "dc_sub None 1682"
  by (dc_eval dc_nc_1682)

lemma dc_nc_1683: "dc_sub None 1683"
  by (dc_eval dc_nc_1683)

lemma dc_nc_1684: "dc_sub None 1684"
  by (dc_eval dc_nc_1684)

lemma dc_nc_1685: "dc_sub None 1685"
  by (dc_eval dc_nc_1685)

lemma dc_nc_1686: "dc_sub None 1686"
  by (dc_eval dc_nc_1686)

lemma dc_nc_1687: "dc_sub None 1687"
  by (dc_eval dc_nc_1687)

lemma dc_nc_1688: "dc_sub None 1688"
  by (dc_eval dc_nc_1688)

lemma dc_nc_1689: "dc_sub None 1689"
  by (dc_eval dc_nc_1689)

lemma dc_nc_1690: "dc_sub None 1690"
  by (dc_eval dc_nc_1690)

lemma dc_nc_1691: "dc_sub None 1691"
  by (dc_eval dc_nc_1691)

lemma dc_nc_1692: "dc_sub None 1692"
  by (dc_eval dc_nc_1692)

lemma dc_nc_1693: "dc_sub None 1693"
  by (dc_eval dc_nc_1693)

lemma dc_nc_1694: "dc_sub None 1694"
  by (dc_eval dc_nc_1694)

lemma dc_nc_1695: "dc_sub None 1695"
  by (dc_eval dc_nc_1695)

lemma upt_nc_105: "[1680..<1696] = [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]"
  by (simp add: upt_rec)

lemma sec_nc_105: "\<forall>j\<in>{16 * 105..<16 * 105 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 105..<16 * 105 + 16}"
  then have "j \<in> set [1680..<1696]" unfolding set_upt by simp
  then have "j \<in> set [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]" unfolding upt_nc_105 .
  then show "dc_sub None j" using dc_nc_1680 dc_nc_1681 dc_nc_1682 dc_nc_1683 dc_nc_1684 dc_nc_1685 dc_nc_1686 dc_nc_1687 dc_nc_1688 dc_nc_1689 dc_nc_1690 dc_nc_1691 dc_nc_1692 dc_nc_1693 dc_nc_1694 dc_nc_1695
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
