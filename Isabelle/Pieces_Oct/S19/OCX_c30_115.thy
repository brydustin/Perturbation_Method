theory OCX_c30_115
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1840: "oc_sub oc_b30 1840"
  by (oc_eval oc_c30_1840)

lemma oc_c30_1841: "oc_sub oc_b30 1841"
  by (oc_eval oc_c30_1841)

lemma oc_c30_1842: "oc_sub oc_b30 1842"
  by (oc_eval oc_c30_1842)

lemma oc_c30_1843: "oc_sub oc_b30 1843"
  by (oc_eval oc_c30_1843)

lemma oc_c30_1844: "oc_sub oc_b30 1844"
  by (oc_eval oc_c30_1844)

lemma oc_c30_1845: "oc_sub oc_b30 1845"
  by (oc_eval oc_c30_1845)

lemma oc_c30_1846: "oc_sub oc_b30 1846"
  by (oc_eval oc_c30_1846)

lemma oc_c30_1847: "oc_sub oc_b30 1847"
  by (oc_eval oc_c30_1847)

lemma oc_c30_1848: "oc_sub oc_b30 1848"
  by (oc_eval oc_c30_1848)

lemma oc_c30_1849: "oc_sub oc_b30 1849"
  by (oc_eval oc_c30_1849)

lemma oc_c30_1850: "oc_sub oc_b30 1850"
  by (oc_eval oc_c30_1850)

lemma oc_c30_1851: "oc_sub oc_b30 1851"
  by (oc_eval oc_c30_1851)

lemma oc_c30_1852: "oc_sub oc_b30 1852"
  by (oc_eval oc_c30_1852)

lemma oc_c30_1853: "oc_sub oc_b30 1853"
  by (oc_eval oc_c30_1853)

lemma oc_c30_1854: "oc_sub oc_b30 1854"
  by (oc_eval oc_c30_1854)

lemma oc_c30_1855: "oc_sub oc_b30 1855"
  by (oc_eval oc_c30_1855)

lemma upt_c30_115: "[1840..<1856] = [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]"
  by (simp add: upt_rec)

lemma sec_c30_115: "\<forall>j\<in>{16 * 115..<16 * 115 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 115..<16 * 115 + 16}"
  then have "j \<in> set [1840..<1856]" unfolding set_upt by simp
  then have "j \<in> set [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]" unfolding upt_c30_115 .
  then show "oc_sub oc_b30 j" using oc_c30_1840 oc_c30_1841 oc_c30_1842 oc_c30_1843 oc_c30_1844 oc_c30_1845 oc_c30_1846 oc_c30_1847 oc_c30_1848 oc_c30_1849 oc_c30_1850 oc_c30_1851 oc_c30_1852 oc_c30_1853 oc_c30_1854 oc_c30_1855
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
