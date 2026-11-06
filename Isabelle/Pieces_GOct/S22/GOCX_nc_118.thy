theory GOCX_nc_118
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1888: "goc_sub None 1888"
  by (goc_eval goc_nc_1888)

lemma goc_nc_1889: "goc_sub None 1889"
  by (goc_eval goc_nc_1889)

lemma goc_nc_1890: "goc_sub None 1890"
  by (goc_eval goc_nc_1890)

lemma goc_nc_1891: "goc_sub None 1891"
  by (goc_eval goc_nc_1891)

lemma goc_nc_1892: "goc_sub None 1892"
  by (goc_eval goc_nc_1892)

lemma goc_nc_1893: "goc_sub None 1893"
  by (goc_eval goc_nc_1893)

lemma goc_nc_1894: "goc_sub None 1894"
  by (goc_eval goc_nc_1894)

lemma goc_nc_1895: "goc_sub None 1895"
  by (goc_eval goc_nc_1895)

lemma goc_nc_1896: "goc_sub None 1896"
  by (goc_eval goc_nc_1896)

lemma goc_nc_1897: "goc_sub None 1897"
  by (goc_eval goc_nc_1897)

lemma goc_nc_1898: "goc_sub None 1898"
  by (goc_eval goc_nc_1898)

lemma goc_nc_1899: "goc_sub None 1899"
  by (goc_eval goc_nc_1899)

lemma goc_nc_1900: "goc_sub None 1900"
  by (goc_eval goc_nc_1900)

lemma goc_nc_1901: "goc_sub None 1901"
  by (goc_eval goc_nc_1901)

lemma goc_nc_1902: "goc_sub None 1902"
  by (goc_eval goc_nc_1902)

lemma goc_nc_1903: "goc_sub None 1903"
  by (goc_eval goc_nc_1903)

lemma gupt_nc_118: "[1888..<1904] = [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]"
  by (simp add: upt_rec)

lemma gsec_nc_118: "\<forall>j\<in>{16 * 118..<16 * 118 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 118..<16 * 118 + 16}"
  then have "j \<in> set [1888..<1904]" unfolding set_upt by simp
  then have "j \<in> set [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]" unfolding gupt_nc_118 .
  then show "goc_sub None j" using goc_nc_1888 goc_nc_1889 goc_nc_1890 goc_nc_1891 goc_nc_1892 goc_nc_1893 goc_nc_1894 goc_nc_1895 goc_nc_1896 goc_nc_1897 goc_nc_1898 goc_nc_1899 goc_nc_1900 goc_nc_1901 goc_nc_1902 goc_nc_1903
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
