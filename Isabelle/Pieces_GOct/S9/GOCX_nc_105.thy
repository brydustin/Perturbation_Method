theory GOCX_nc_105
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1680: "goc_sub None 1680"
  by (goc_eval goc_nc_1680)

lemma goc_nc_1681: "goc_sub None 1681"
  by (goc_eval goc_nc_1681)

lemma goc_nc_1682: "goc_sub None 1682"
  by (goc_eval goc_nc_1682)

lemma goc_nc_1683: "goc_sub None 1683"
  by (goc_eval goc_nc_1683)

lemma goc_nc_1684: "goc_sub None 1684"
  by (goc_eval goc_nc_1684)

lemma goc_nc_1685: "goc_sub None 1685"
  by (goc_eval goc_nc_1685)

lemma goc_nc_1686: "goc_sub None 1686"
  by (goc_eval goc_nc_1686)

lemma goc_nc_1687: "goc_sub None 1687"
  by (goc_eval goc_nc_1687)

lemma goc_nc_1688: "goc_sub None 1688"
  by (goc_eval goc_nc_1688)

lemma goc_nc_1689: "goc_sub None 1689"
  by (goc_eval goc_nc_1689)

lemma goc_nc_1690: "goc_sub None 1690"
  by (goc_eval goc_nc_1690)

lemma goc_nc_1691: "goc_sub None 1691"
  by (goc_eval goc_nc_1691)

lemma goc_nc_1692: "goc_sub None 1692"
  by (goc_eval goc_nc_1692)

lemma goc_nc_1693: "goc_sub None 1693"
  by (goc_eval goc_nc_1693)

lemma goc_nc_1694: "goc_sub None 1694"
  by (goc_eval goc_nc_1694)

lemma goc_nc_1695: "goc_sub None 1695"
  by (goc_eval goc_nc_1695)

lemma gupt_nc_105: "[1680..<1696] = [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]"
  by (simp add: upt_rec)

lemma gsec_nc_105: "\<forall>j\<in>{16 * 105..<16 * 105 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 105..<16 * 105 + 16}"
  then have "j \<in> set [1680..<1696]" unfolding set_upt by simp
  then have "j \<in> set [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]" unfolding gupt_nc_105 .
  then show "goc_sub None j" using goc_nc_1680 goc_nc_1681 goc_nc_1682 goc_nc_1683 goc_nc_1684 goc_nc_1685 goc_nc_1686 goc_nc_1687 goc_nc_1688 goc_nc_1689 goc_nc_1690 goc_nc_1691 goc_nc_1692 goc_nc_1693 goc_nc_1694 goc_nc_1695
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
