theory DCX_c30_109
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1744: "dc_sub dc_b30 1744"
  by (dc_eval dc_c30_1744)

lemma dc_c30_1745: "dc_sub dc_b30 1745"
  by (dc_eval dc_c30_1745)

lemma dc_c30_1746: "dc_sub dc_b30 1746"
  by (dc_eval dc_c30_1746)

lemma dc_c30_1747: "dc_sub dc_b30 1747"
  by (dc_eval dc_c30_1747)

lemma dc_c30_1748: "dc_sub dc_b30 1748"
  by (dc_eval dc_c30_1748)

lemma dc_c30_1749: "dc_sub dc_b30 1749"
  by (dc_eval dc_c30_1749)

lemma dc_c30_1750: "dc_sub dc_b30 1750"
  by (dc_eval dc_c30_1750)

lemma dc_c30_1751: "dc_sub dc_b30 1751"
  by (dc_eval dc_c30_1751)

lemma dc_c30_1752: "dc_sub dc_b30 1752"
  by (dc_eval dc_c30_1752)

lemma dc_c30_1753: "dc_sub dc_b30 1753"
  by (dc_eval dc_c30_1753)

lemma dc_c30_1754: "dc_sub dc_b30 1754"
  by (dc_eval dc_c30_1754)

lemma dc_c30_1755: "dc_sub dc_b30 1755"
  by (dc_eval dc_c30_1755)

lemma dc_c30_1756: "dc_sub dc_b30 1756"
  by (dc_eval dc_c30_1756)

lemma dc_c30_1757: "dc_sub dc_b30 1757"
  by (dc_eval dc_c30_1757)

lemma dc_c30_1758: "dc_sub dc_b30 1758"
  by (dc_eval dc_c30_1758)

lemma dc_c30_1759: "dc_sub dc_b30 1759"
  by (dc_eval dc_c30_1759)

lemma upt_c30_109: "[1744..<1760] = [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]"
  by (simp add: upt_rec)

lemma sec_c30_109: "\<forall>j\<in>{16 * 109..<16 * 109 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 109..<16 * 109 + 16}"
  then have "j \<in> set [1744..<1760]" unfolding set_upt by simp
  then have "j \<in> set [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]" unfolding upt_c30_109 .
  then show "dc_sub dc_b30 j" using dc_c30_1744 dc_c30_1745 dc_c30_1746 dc_c30_1747 dc_c30_1748 dc_c30_1749 dc_c30_1750 dc_c30_1751 dc_c30_1752 dc_c30_1753 dc_c30_1754 dc_c30_1755 dc_c30_1756 dc_c30_1757 dc_c30_1758 dc_c30_1759
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
