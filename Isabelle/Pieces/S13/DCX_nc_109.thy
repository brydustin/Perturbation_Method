theory DCX_nc_109
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1744: "dc_sub None 1744"
  by (dc_eval dc_nc_1744)

lemma dc_nc_1745: "dc_sub None 1745"
  by (dc_eval dc_nc_1745)

lemma dc_nc_1746: "dc_sub None 1746"
  by (dc_eval dc_nc_1746)

lemma dc_nc_1747: "dc_sub None 1747"
  by (dc_eval dc_nc_1747)

lemma dc_nc_1748: "dc_sub None 1748"
  by (dc_eval dc_nc_1748)

lemma dc_nc_1749: "dc_sub None 1749"
  by (dc_eval dc_nc_1749)

lemma dc_nc_1750: "dc_sub None 1750"
  by (dc_eval dc_nc_1750)

lemma dc_nc_1751: "dc_sub None 1751"
  by (dc_eval dc_nc_1751)

lemma dc_nc_1752: "dc_sub None 1752"
  by (dc_eval dc_nc_1752)

lemma dc_nc_1753: "dc_sub None 1753"
  by (dc_eval dc_nc_1753)

lemma dc_nc_1754: "dc_sub None 1754"
  by (dc_eval dc_nc_1754)

lemma dc_nc_1755: "dc_sub None 1755"
  by (dc_eval dc_nc_1755)

lemma dc_nc_1756: "dc_sub None 1756"
  by (dc_eval dc_nc_1756)

lemma dc_nc_1757: "dc_sub None 1757"
  by (dc_eval dc_nc_1757)

lemma dc_nc_1758: "dc_sub None 1758"
  by (dc_eval dc_nc_1758)

lemma dc_nc_1759: "dc_sub None 1759"
  by (dc_eval dc_nc_1759)

lemma upt_nc_109: "[1744..<1760] = [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]"
  by (simp add: upt_rec)

lemma sec_nc_109: "\<forall>j\<in>{16 * 109..<16 * 109 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 109..<16 * 109 + 16}"
  then have "j \<in> set [1744..<1760]" unfolding set_upt by simp
  then have "j \<in> set [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]" unfolding upt_nc_109 .
  then show "dc_sub None j" using dc_nc_1744 dc_nc_1745 dc_nc_1746 dc_nc_1747 dc_nc_1748 dc_nc_1749 dc_nc_1750 dc_nc_1751 dc_nc_1752 dc_nc_1753 dc_nc_1754 dc_nc_1755 dc_nc_1756 dc_nc_1757 dc_nc_1758 dc_nc_1759
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
