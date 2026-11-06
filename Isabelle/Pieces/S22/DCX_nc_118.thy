theory DCX_nc_118
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1888: "dc_sub None 1888"
  by (dc_eval dc_nc_1888)

lemma dc_nc_1889: "dc_sub None 1889"
  by (dc_eval dc_nc_1889)

lemma dc_nc_1890: "dc_sub None 1890"
  by (dc_eval dc_nc_1890)

lemma dc_nc_1891: "dc_sub None 1891"
  by (dc_eval dc_nc_1891)

lemma dc_nc_1892: "dc_sub None 1892"
  by (dc_eval dc_nc_1892)

lemma dc_nc_1893: "dc_sub None 1893"
  by (dc_eval dc_nc_1893)

lemma dc_nc_1894: "dc_sub None 1894"
  by (dc_eval dc_nc_1894)

lemma dc_nc_1895: "dc_sub None 1895"
  by (dc_eval dc_nc_1895)

lemma dc_nc_1896: "dc_sub None 1896"
  by (dc_eval dc_nc_1896)

lemma dc_nc_1897: "dc_sub None 1897"
  by (dc_eval dc_nc_1897)

lemma dc_nc_1898: "dc_sub None 1898"
  by (dc_eval dc_nc_1898)

lemma dc_nc_1899: "dc_sub None 1899"
  by (dc_eval dc_nc_1899)

lemma dc_nc_1900: "dc_sub None 1900"
  by (dc_eval dc_nc_1900)

lemma dc_nc_1901: "dc_sub None 1901"
  by (dc_eval dc_nc_1901)

lemma dc_nc_1902: "dc_sub None 1902"
  by (dc_eval dc_nc_1902)

lemma dc_nc_1903: "dc_sub None 1903"
  by (dc_eval dc_nc_1903)

lemma upt_nc_118: "[1888..<1904] = [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]"
  by (simp add: upt_rec)

lemma sec_nc_118: "\<forall>j\<in>{16 * 118..<16 * 118 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 118..<16 * 118 + 16}"
  then have "j \<in> set [1888..<1904]" unfolding set_upt by simp
  then have "j \<in> set [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]" unfolding upt_nc_118 .
  then show "dc_sub None j" using dc_nc_1888 dc_nc_1889 dc_nc_1890 dc_nc_1891 dc_nc_1892 dc_nc_1893 dc_nc_1894 dc_nc_1895 dc_nc_1896 dc_nc_1897 dc_nc_1898 dc_nc_1899 dc_nc_1900 dc_nc_1901 dc_nc_1902 dc_nc_1903
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
