theory GDCX_nc_118
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1888: "gdc_sub None 1888"
  by (gdc_eval gdc_nc_1888)

lemma gdc_nc_1889: "gdc_sub None 1889"
  by (gdc_eval gdc_nc_1889)

lemma gdc_nc_1890: "gdc_sub None 1890"
  by (gdc_eval gdc_nc_1890)

lemma gdc_nc_1891: "gdc_sub None 1891"
  by (gdc_eval gdc_nc_1891)

lemma gdc_nc_1892: "gdc_sub None 1892"
  by (gdc_eval gdc_nc_1892)

lemma gdc_nc_1893: "gdc_sub None 1893"
  by (gdc_eval gdc_nc_1893)

lemma gdc_nc_1894: "gdc_sub None 1894"
  by (gdc_eval gdc_nc_1894)

lemma gdc_nc_1895: "gdc_sub None 1895"
  by (gdc_eval gdc_nc_1895)

lemma gdc_nc_1896: "gdc_sub None 1896"
  by (gdc_eval gdc_nc_1896)

lemma gdc_nc_1897: "gdc_sub None 1897"
  by (gdc_eval gdc_nc_1897)

lemma gdc_nc_1898: "gdc_sub None 1898"
  by (gdc_eval gdc_nc_1898)

lemma gdc_nc_1899: "gdc_sub None 1899"
  by (gdc_eval gdc_nc_1899)

lemma gdc_nc_1900: "gdc_sub None 1900"
  by (gdc_eval gdc_nc_1900)

lemma gdc_nc_1901: "gdc_sub None 1901"
  by (gdc_eval gdc_nc_1901)

lemma gdc_nc_1902: "gdc_sub None 1902"
  by (gdc_eval gdc_nc_1902)

lemma gdc_nc_1903: "gdc_sub None 1903"
  by (gdc_eval gdc_nc_1903)

lemma gupt_nc_118: "[1888..<1904] = [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]"
  by (simp add: upt_rec)

lemma gsec_nc_118: "\<forall>j\<in>{16 * 118..<16 * 118 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 118..<16 * 118 + 16}"
  then have "j \<in> set [1888..<1904]" unfolding set_upt by simp
  then have "j \<in> set [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]" unfolding gupt_nc_118 .
  then show "gdc_sub None j" using gdc_nc_1888 gdc_nc_1889 gdc_nc_1890 gdc_nc_1891 gdc_nc_1892 gdc_nc_1893 gdc_nc_1894 gdc_nc_1895 gdc_nc_1896 gdc_nc_1897 gdc_nc_1898 gdc_nc_1899 gdc_nc_1900 gdc_nc_1901 gdc_nc_1902 gdc_nc_1903
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
