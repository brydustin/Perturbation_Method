theory OCX_nc_109
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1744: "oc_sub None 1744"
  by (oc_eval oc_nc_1744)

lemma oc_nc_1745: "oc_sub None 1745"
  by (oc_eval oc_nc_1745)

lemma oc_nc_1746: "oc_sub None 1746"
  by (oc_eval oc_nc_1746)

lemma oc_nc_1747: "oc_sub None 1747"
  by (oc_eval oc_nc_1747)

lemma oc_nc_1748: "oc_sub None 1748"
  by (oc_eval oc_nc_1748)

lemma oc_nc_1749: "oc_sub None 1749"
  by (oc_eval oc_nc_1749)

lemma oc_nc_1750: "oc_sub None 1750"
  by (oc_eval oc_nc_1750)

lemma oc_nc_1751: "oc_sub None 1751"
  by (oc_eval oc_nc_1751)

lemma oc_nc_1752: "oc_sub None 1752"
  by (oc_eval oc_nc_1752)

lemma oc_nc_1753: "oc_sub None 1753"
  by (oc_eval oc_nc_1753)

lemma oc_nc_1754: "oc_sub None 1754"
  by (oc_eval oc_nc_1754)

lemma oc_nc_1755: "oc_sub None 1755"
  by (oc_eval oc_nc_1755)

lemma oc_nc_1756: "oc_sub None 1756"
  by (oc_eval oc_nc_1756)

lemma oc_nc_1757: "oc_sub None 1757"
  by (oc_eval oc_nc_1757)

lemma oc_nc_1758: "oc_sub None 1758"
  by (oc_eval oc_nc_1758)

lemma oc_nc_1759: "oc_sub None 1759"
  by (oc_eval oc_nc_1759)

lemma upt_nc_109: "[1744..<1760] = [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]"
  by (simp add: upt_rec)

lemma sec_nc_109: "\<forall>j\<in>{16 * 109..<16 * 109 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 109..<16 * 109 + 16}"
  then have "j \<in> set [1744..<1760]" unfolding set_upt by simp
  then have "j \<in> set [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]" unfolding upt_nc_109 .
  then show "oc_sub None j" using oc_nc_1744 oc_nc_1745 oc_nc_1746 oc_nc_1747 oc_nc_1748 oc_nc_1749 oc_nc_1750 oc_nc_1751 oc_nc_1752 oc_nc_1753 oc_nc_1754 oc_nc_1755 oc_nc_1756 oc_nc_1757 oc_nc_1758 oc_nc_1759
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
