theory GDCX_nc_109
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1744: "gdc_sub None 1744"
  by (gdc_eval gdc_nc_1744)

lemma gdc_nc_1745: "gdc_sub None 1745"
  by (gdc_eval gdc_nc_1745)

lemma gdc_nc_1746: "gdc_sub None 1746"
  by (gdc_eval gdc_nc_1746)

lemma gdc_nc_1747: "gdc_sub None 1747"
  by (gdc_eval gdc_nc_1747)

lemma gdc_nc_1748: "gdc_sub None 1748"
  by (gdc_eval gdc_nc_1748)

lemma gdc_nc_1749: "gdc_sub None 1749"
  by (gdc_eval gdc_nc_1749)

lemma gdc_nc_1750: "gdc_sub None 1750"
  by (gdc_eval gdc_nc_1750)

lemma gdc_nc_1751: "gdc_sub None 1751"
  by (gdc_eval gdc_nc_1751)

lemma gdc_nc_1752: "gdc_sub None 1752"
  by (gdc_eval gdc_nc_1752)

lemma gdc_nc_1753: "gdc_sub None 1753"
  by (gdc_eval gdc_nc_1753)

lemma gdc_nc_1754: "gdc_sub None 1754"
  by (gdc_eval gdc_nc_1754)

lemma gdc_nc_1755: "gdc_sub None 1755"
  by (gdc_eval gdc_nc_1755)

lemma gdc_nc_1756: "gdc_sub None 1756"
  by (gdc_eval gdc_nc_1756)

lemma gdc_nc_1757: "gdc_sub None 1757"
  by (gdc_eval gdc_nc_1757)

lemma gdc_nc_1758: "gdc_sub None 1758"
  by (gdc_eval gdc_nc_1758)

lemma gdc_nc_1759: "gdc_sub None 1759"
  by (gdc_eval gdc_nc_1759)

lemma gupt_nc_109: "[1744..<1760] = [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]"
  by (simp add: upt_rec)

lemma gsec_nc_109: "\<forall>j\<in>{16 * 109..<16 * 109 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 109..<16 * 109 + 16}"
  then have "j \<in> set [1744..<1760]" unfolding set_upt by simp
  then have "j \<in> set [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]" unfolding gupt_nc_109 .
  then show "gdc_sub None j" using gdc_nc_1744 gdc_nc_1745 gdc_nc_1746 gdc_nc_1747 gdc_nc_1748 gdc_nc_1749 gdc_nc_1750 gdc_nc_1751 gdc_nc_1752 gdc_nc_1753 gdc_nc_1754 gdc_nc_1755 gdc_nc_1756 gdc_nc_1757 gdc_nc_1758 gdc_nc_1759
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
