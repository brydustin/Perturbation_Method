theory DCX_nc_115
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1840: "dc_sub None 1840"
  by (dc_eval dc_nc_1840)

lemma dc_nc_1841: "dc_sub None 1841"
  by (dc_eval dc_nc_1841)

lemma dc_nc_1842: "dc_sub None 1842"
  by (dc_eval dc_nc_1842)

lemma dc_nc_1843: "dc_sub None 1843"
  by (dc_eval dc_nc_1843)

lemma dc_nc_1844: "dc_sub None 1844"
  by (dc_eval dc_nc_1844)

lemma dc_nc_1845: "dc_sub None 1845"
  by (dc_eval dc_nc_1845)

lemma dc_nc_1846: "dc_sub None 1846"
  by (dc_eval dc_nc_1846)

lemma dc_nc_1847: "dc_sub None 1847"
  by (dc_eval dc_nc_1847)

lemma dc_nc_1848: "dc_sub None 1848"
  by (dc_eval dc_nc_1848)

lemma dc_nc_1849: "dc_sub None 1849"
  by (dc_eval dc_nc_1849)

lemma dc_nc_1850: "dc_sub None 1850"
  by (dc_eval dc_nc_1850)

lemma dc_nc_1851: "dc_sub None 1851"
  by (dc_eval dc_nc_1851)

lemma dc_nc_1852: "dc_sub None 1852"
  by (dc_eval dc_nc_1852)

lemma dc_nc_1853: "dc_sub None 1853"
  by (dc_eval dc_nc_1853)

lemma dc_nc_1854: "dc_sub None 1854"
  by (dc_eval dc_nc_1854)

lemma dc_nc_1855: "dc_sub None 1855"
  by (dc_eval dc_nc_1855)

lemma upt_nc_115: "[1840..<1856] = [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]"
  by (simp add: upt_rec)

lemma sec_nc_115: "\<forall>j\<in>{16 * 115..<16 * 115 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 115..<16 * 115 + 16}"
  then have "j \<in> set [1840..<1856]" unfolding set_upt by simp
  then have "j \<in> set [1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855]" unfolding upt_nc_115 .
  then show "dc_sub None j" using dc_nc_1840 dc_nc_1841 dc_nc_1842 dc_nc_1843 dc_nc_1844 dc_nc_1845 dc_nc_1846 dc_nc_1847 dc_nc_1848 dc_nc_1849 dc_nc_1850 dc_nc_1851 dc_nc_1852 dc_nc_1853 dc_nc_1854 dc_nc_1855
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
