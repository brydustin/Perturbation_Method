theory DCX_c30_115
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1840: "dc_sub dc_b30 1840"
  by (dc_eval dc_c30_1840)

lemma dc_c30_1841: "dc_sub dc_b30 1841"
  by (dc_eval dc_c30_1841)

lemma dc_c30_1842: "dc_sub dc_b30 1842"
  by (dc_eval dc_c30_1842)

lemma dc_c30_1843: "dc_sub dc_b30 1843"
  by (dc_eval dc_c30_1843)

lemma dc_c30_1844: "dc_sub dc_b30 1844"
  by (dc_eval dc_c30_1844)

lemma dc_c30_1845: "dc_sub dc_b30 1845"
  by (dc_eval dc_c30_1845)

lemma dc_c30_1846: "dc_sub dc_b30 1846"
  by (dc_eval dc_c30_1846)

lemma dc_c30_1847: "dc_sub dc_b30 1847"
  by (dc_eval dc_c30_1847)

lemma dc_c30_1848: "dc_sub dc_b30 1848"
  by (dc_eval dc_c30_1848)

lemma dc_c30_1849: "dc_sub dc_b30 1849"
  by (dc_eval dc_c30_1849)

lemma dc_c30_1850: "dc_sub dc_b30 1850"
  by (dc_eval dc_c30_1850)

lemma dc_c30_1851: "dc_sub dc_b30 1851"
  by (dc_eval dc_c30_1851)

lemma dc_c30_1852: "dc_sub dc_b30 1852"
  by (dc_eval dc_c30_1852)

lemma dc_c30_1853: "dc_sub dc_b30 1853"
  by (dc_eval dc_c30_1853)

lemma dc_c30_1854: "dc_sub dc_b30 1854"
  by (dc_eval dc_c30_1854)

lemma dc_c30_1855: "dc_sub dc_b30 1855"
  by (dc_eval dc_c30_1855)

lemma upt_c30_115: "[1840..<1856] = [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]"
  by (simp add: upt_rec)

lemma sec_c30_115: "\<forall>j\<in>{16 * 115..<16 * 115 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 115..<16 * 115 + 16}"
  then have "j \<in> set [1840..<1856]" unfolding set_upt by simp
  then have "j \<in> set [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]" unfolding upt_c30_115 .
  then show "dc_sub dc_b30 j" using dc_c30_1840 dc_c30_1841 dc_c30_1842 dc_c30_1843 dc_c30_1844 dc_c30_1845 dc_c30_1846 dc_c30_1847 dc_c30_1848 dc_c30_1849 dc_c30_1850 dc_c30_1851 dc_c30_1852 dc_c30_1853 dc_c30_1854 dc_c30_1855
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
