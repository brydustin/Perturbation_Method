theory OCX_nc_115
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1840: "oc_sub None 1840"
  by (oc_eval oc_nc_1840)

lemma oc_nc_1841: "oc_sub None 1841"
  by (oc_eval oc_nc_1841)

lemma oc_nc_1842: "oc_sub None 1842"
  by (oc_eval oc_nc_1842)

lemma oc_nc_1843: "oc_sub None 1843"
  by (oc_eval oc_nc_1843)

lemma oc_nc_1844: "oc_sub None 1844"
  by (oc_eval oc_nc_1844)

lemma oc_nc_1845: "oc_sub None 1845"
  by (oc_eval oc_nc_1845)

lemma oc_nc_1846: "oc_sub None 1846"
  by (oc_eval oc_nc_1846)

lemma oc_nc_1847: "oc_sub None 1847"
  by (oc_eval oc_nc_1847)

lemma oc_nc_1848: "oc_sub None 1848"
  by (oc_eval oc_nc_1848)

lemma oc_nc_1849: "oc_sub None 1849"
  by (oc_eval oc_nc_1849)

lemma oc_nc_1850: "oc_sub None 1850"
  by (oc_eval oc_nc_1850)

lemma oc_nc_1851: "oc_sub None 1851"
  by (oc_eval oc_nc_1851)

lemma oc_nc_1852: "oc_sub None 1852"
  by (oc_eval oc_nc_1852)

lemma oc_nc_1853: "oc_sub None 1853"
  by (oc_eval oc_nc_1853)

lemma oc_nc_1854: "oc_sub None 1854"
  by (oc_eval oc_nc_1854)

lemma oc_nc_1855: "oc_sub None 1855"
  by (oc_eval oc_nc_1855)

lemma upt_nc_115: "[1840..<1856] = [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]"
  by (simp add: upt_rec)

lemma sec_nc_115: "\<forall>j\<in>{16 * 115..<16 * 115 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 115..<16 * 115 + 16}"
  then have "j \<in> set [1840..<1856]" unfolding set_upt by simp
  then have "j \<in> set [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]" unfolding upt_nc_115 .
  then show "oc_sub None j" using oc_nc_1840 oc_nc_1841 oc_nc_1842 oc_nc_1843 oc_nc_1844 oc_nc_1845 oc_nc_1846 oc_nc_1847 oc_nc_1848 oc_nc_1849 oc_nc_1850 oc_nc_1851 oc_nc_1852 oc_nc_1853 oc_nc_1854 oc_nc_1855
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
