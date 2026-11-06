theory GDCX_nc_115
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1840: "gdc_sub None 1840"
  by (gdc_eval gdc_nc_1840)

lemma gdc_nc_1841: "gdc_sub None 1841"
  by (gdc_eval gdc_nc_1841)

lemma gdc_nc_1842: "gdc_sub None 1842"
  by (gdc_eval gdc_nc_1842)

lemma gdc_nc_1843: "gdc_sub None 1843"
  by (gdc_eval gdc_nc_1843)

lemma gdc_nc_1844: "gdc_sub None 1844"
  by (gdc_eval gdc_nc_1844)

lemma gdc_nc_1845: "gdc_sub None 1845"
  by (gdc_eval gdc_nc_1845)

lemma gdc_nc_1846: "gdc_sub None 1846"
  by (gdc_eval gdc_nc_1846)

lemma gdc_nc_1847: "gdc_sub None 1847"
  by (gdc_eval gdc_nc_1847)

lemma gdc_nc_1848: "gdc_sub None 1848"
  by (gdc_eval gdc_nc_1848)

lemma gdc_nc_1849: "gdc_sub None 1849"
  by (gdc_eval gdc_nc_1849)

lemma gdc_nc_1850: "gdc_sub None 1850"
  by (gdc_eval gdc_nc_1850)

lemma gdc_nc_1851: "gdc_sub None 1851"
  by (gdc_eval gdc_nc_1851)

lemma gdc_nc_1852: "gdc_sub None 1852"
  by (gdc_eval gdc_nc_1852)

lemma gdc_nc_1853: "gdc_sub None 1853"
  by (gdc_eval gdc_nc_1853)

lemma gdc_nc_1854: "gdc_sub None 1854"
  by (gdc_eval gdc_nc_1854)

lemma gdc_nc_1855: "gdc_sub None 1855"
  by (gdc_eval gdc_nc_1855)

lemma gupt_nc_115: "[1840..<1856] = [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]"
  by (simp add: upt_rec)

lemma gsec_nc_115: "\<forall>j\<in>{16 * 115..<16 * 115 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 115..<16 * 115 + 16}"
  then have "j \<in> set [1840..<1856]" unfolding set_upt by simp
  then have "j \<in> set [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]" unfolding gupt_nc_115 .
  then show "gdc_sub None j" using gdc_nc_1840 gdc_nc_1841 gdc_nc_1842 gdc_nc_1843 gdc_nc_1844 gdc_nc_1845 gdc_nc_1846 gdc_nc_1847 gdc_nc_1848 gdc_nc_1849 gdc_nc_1850 gdc_nc_1851 gdc_nc_1852 gdc_nc_1853 gdc_nc_1854 gdc_nc_1855
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
