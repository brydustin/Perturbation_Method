theory GOCX_nc_109
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1744: "goc_sub None 1744"
  by (goc_eval goc_nc_1744)

lemma goc_nc_1745: "goc_sub None 1745"
  by (goc_eval goc_nc_1745)

lemma goc_nc_1746: "goc_sub None 1746"
  by (goc_eval goc_nc_1746)

lemma goc_nc_1747: "goc_sub None 1747"
  by (goc_eval goc_nc_1747)

lemma goc_nc_1748: "goc_sub None 1748"
  by (goc_eval goc_nc_1748)

lemma goc_nc_1749: "goc_sub None 1749"
  by (goc_eval goc_nc_1749)

lemma goc_nc_1750: "goc_sub None 1750"
  by (goc_eval goc_nc_1750)

lemma goc_nc_1751: "goc_sub None 1751"
  by (goc_eval goc_nc_1751)

lemma goc_nc_1752: "goc_sub None 1752"
  by (goc_eval goc_nc_1752)

lemma goc_nc_1753: "goc_sub None 1753"
  by (goc_eval goc_nc_1753)

lemma goc_nc_1754: "goc_sub None 1754"
  by (goc_eval goc_nc_1754)

lemma goc_nc_1755: "goc_sub None 1755"
  by (goc_eval goc_nc_1755)

lemma goc_nc_1756: "goc_sub None 1756"
  by (goc_eval goc_nc_1756)

lemma goc_nc_1757: "goc_sub None 1757"
  by (goc_eval goc_nc_1757)

lemma goc_nc_1758: "goc_sub None 1758"
  by (goc_eval goc_nc_1758)

lemma goc_nc_1759: "goc_sub None 1759"
  by (goc_eval goc_nc_1759)

lemma gupt_nc_109: "[1744..<1760] = [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]"
  by (simp add: upt_rec)

lemma gsec_nc_109: "\<forall>j\<in>{16 * 109..<16 * 109 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 109..<16 * 109 + 16}"
  then have "j \<in> set [1744..<1760]" unfolding set_upt by simp
  then have "j \<in> set [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]" unfolding gupt_nc_109 .
  then show "goc_sub None j" using goc_nc_1744 goc_nc_1745 goc_nc_1746 goc_nc_1747 goc_nc_1748 goc_nc_1749 goc_nc_1750 goc_nc_1751 goc_nc_1752 goc_nc_1753 goc_nc_1754 goc_nc_1755 goc_nc_1756 goc_nc_1757 goc_nc_1758 goc_nc_1759
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
