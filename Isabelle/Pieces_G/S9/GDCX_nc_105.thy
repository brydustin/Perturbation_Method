theory GDCX_nc_105
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1680: "gdc_sub None 1680"
  by (gdc_eval gdc_nc_1680)

lemma gdc_nc_1681: "gdc_sub None 1681"
  by (gdc_eval gdc_nc_1681)

lemma gdc_nc_1682: "gdc_sub None 1682"
  by (gdc_eval gdc_nc_1682)

lemma gdc_nc_1683: "gdc_sub None 1683"
  by (gdc_eval gdc_nc_1683)

lemma gdc_nc_1684: "gdc_sub None 1684"
  by (gdc_eval gdc_nc_1684)

lemma gdc_nc_1685: "gdc_sub None 1685"
  by (gdc_eval gdc_nc_1685)

lemma gdc_nc_1686: "gdc_sub None 1686"
  by (gdc_eval gdc_nc_1686)

lemma gdc_nc_1687: "gdc_sub None 1687"
  by (gdc_eval gdc_nc_1687)

lemma gdc_nc_1688: "gdc_sub None 1688"
  by (gdc_eval gdc_nc_1688)

lemma gdc_nc_1689: "gdc_sub None 1689"
  by (gdc_eval gdc_nc_1689)

lemma gdc_nc_1690: "gdc_sub None 1690"
  by (gdc_eval gdc_nc_1690)

lemma gdc_nc_1691: "gdc_sub None 1691"
  by (gdc_eval gdc_nc_1691)

lemma gdc_nc_1692: "gdc_sub None 1692"
  by (gdc_eval gdc_nc_1692)

lemma gdc_nc_1693: "gdc_sub None 1693"
  by (gdc_eval gdc_nc_1693)

lemma gdc_nc_1694: "gdc_sub None 1694"
  by (gdc_eval gdc_nc_1694)

lemma gdc_nc_1695: "gdc_sub None 1695"
  by (gdc_eval gdc_nc_1695)

lemma gupt_nc_105: "[1680..<1696] = [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]"
  by (simp add: upt_rec)

lemma gsec_nc_105: "\<forall>j\<in>{16 * 105..<16 * 105 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 105..<16 * 105 + 16}"
  then have "j \<in> set [1680..<1696]" unfolding set_upt by simp
  then have "j \<in> set [1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695]" unfolding gupt_nc_105 .
  then show "gdc_sub None j" using gdc_nc_1680 gdc_nc_1681 gdc_nc_1682 gdc_nc_1683 gdc_nc_1684 gdc_nc_1685 gdc_nc_1686 gdc_nc_1687 gdc_nc_1688 gdc_nc_1689 gdc_nc_1690 gdc_nc_1691 gdc_nc_1692 gdc_nc_1693 gdc_nc_1694 gdc_nc_1695
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
