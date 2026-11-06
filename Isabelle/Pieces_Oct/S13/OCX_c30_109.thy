theory OCX_c30_109
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1744: "oc_sub oc_b30 1744"
  by (oc_eval oc_c30_1744)

lemma oc_c30_1745: "oc_sub oc_b30 1745"
  by (oc_eval oc_c30_1745)

lemma oc_c30_1746: "oc_sub oc_b30 1746"
  by (oc_eval oc_c30_1746)

lemma oc_c30_1747: "oc_sub oc_b30 1747"
  by (oc_eval oc_c30_1747)

lemma oc_c30_1748: "oc_sub oc_b30 1748"
  by (oc_eval oc_c30_1748)

lemma oc_c30_1749: "oc_sub oc_b30 1749"
  by (oc_eval oc_c30_1749)

lemma oc_c30_1750: "oc_sub oc_b30 1750"
  by (oc_eval oc_c30_1750)

lemma oc_c30_1751: "oc_sub oc_b30 1751"
  by (oc_eval oc_c30_1751)

lemma oc_c30_1752: "oc_sub oc_b30 1752"
  by (oc_eval oc_c30_1752)

lemma oc_c30_1753: "oc_sub oc_b30 1753"
  by (oc_eval oc_c30_1753)

lemma oc_c30_1754: "oc_sub oc_b30 1754"
  by (oc_eval oc_c30_1754)

lemma oc_c30_1755: "oc_sub oc_b30 1755"
  by (oc_eval oc_c30_1755)

lemma oc_c30_1756: "oc_sub oc_b30 1756"
  by (oc_eval oc_c30_1756)

lemma oc_c30_1757: "oc_sub oc_b30 1757"
  by (oc_eval oc_c30_1757)

lemma oc_c30_1758: "oc_sub oc_b30 1758"
  by (oc_eval oc_c30_1758)

lemma oc_c30_1759: "oc_sub oc_b30 1759"
  by (oc_eval oc_c30_1759)

lemma upt_c30_109: "[1744..<1760] = [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]"
  by (simp add: upt_rec)

lemma sec_c30_109: "\<forall>j\<in>{16 * 109..<16 * 109 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 109..<16 * 109 + 16}"
  then have "j \<in> set [1744..<1760]" unfolding set_upt by simp
  then have "j \<in> set [1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759]" unfolding upt_c30_109 .
  then show "oc_sub oc_b30 j" using oc_c30_1744 oc_c30_1745 oc_c30_1746 oc_c30_1747 oc_c30_1748 oc_c30_1749 oc_c30_1750 oc_c30_1751 oc_c30_1752 oc_c30_1753 oc_c30_1754 oc_c30_1755 oc_c30_1756 oc_c30_1757 oc_c30_1758 oc_c30_1759
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
