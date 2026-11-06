theory GOCX_nc_115
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1840: "goc_sub None 1840"
  by (goc_eval goc_nc_1840)

lemma goc_nc_1841: "goc_sub None 1841"
  by (goc_eval goc_nc_1841)

lemma goc_nc_1842: "goc_sub None 1842"
  by (goc_eval goc_nc_1842)

lemma goc_nc_1843: "goc_sub None 1843"
  by (goc_eval goc_nc_1843)

lemma goc_nc_1844: "goc_sub None 1844"
  by (goc_eval goc_nc_1844)

lemma goc_nc_1845: "goc_sub None 1845"
  by (goc_eval goc_nc_1845)

lemma goc_nc_1846: "goc_sub None 1846"
  by (goc_eval goc_nc_1846)

lemma goc_nc_1847: "goc_sub None 1847"
  by (goc_eval goc_nc_1847)

lemma goc_nc_1848: "goc_sub None 1848"
  by (goc_eval goc_nc_1848)

lemma goc_nc_1849: "goc_sub None 1849"
  by (goc_eval goc_nc_1849)

lemma goc_nc_1850: "goc_sub None 1850"
  by (goc_eval goc_nc_1850)

lemma goc_nc_1851: "goc_sub None 1851"
  by (goc_eval goc_nc_1851)

lemma goc_nc_1852: "goc_sub None 1852"
  by (goc_eval goc_nc_1852)

lemma goc_nc_1853: "goc_sub None 1853"
  by (goc_eval goc_nc_1853)

lemma goc_nc_1854: "goc_sub None 1854"
  by (goc_eval goc_nc_1854)

lemma goc_nc_1855: "goc_sub None 1855"
  by (goc_eval goc_nc_1855)

lemma gupt_nc_115: "[1840..<1856] = [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]"
  by (simp add: upt_rec)

lemma gsec_nc_115: "\<forall>j\<in>{16 * 115..<16 * 115 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 115..<16 * 115 + 16}"
  then have "j \<in> set [1840..<1856]" unfolding set_upt by simp
  then have "j \<in> set [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]" unfolding gupt_nc_115 .
  then show "goc_sub None j" using goc_nc_1840 goc_nc_1841 goc_nc_1842 goc_nc_1843 goc_nc_1844 goc_nc_1845 goc_nc_1846 goc_nc_1847 goc_nc_1848 goc_nc_1849 goc_nc_1850 goc_nc_1851 goc_nc_1852 goc_nc_1853 goc_nc_1854 goc_nc_1855
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
