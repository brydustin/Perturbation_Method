theory DCX_c30_118
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1888: "dc_sub dc_b30 1888"
  by (dc_eval dc_c30_1888)

lemma dc_c30_1889: "dc_sub dc_b30 1889"
  by (dc_eval dc_c30_1889)

lemma dc_c30_1890: "dc_sub dc_b30 1890"
  by (dc_eval dc_c30_1890)

lemma dc_c30_1891: "dc_sub dc_b30 1891"
  by (dc_eval dc_c30_1891)

lemma dc_c30_1892: "dc_sub dc_b30 1892"
  by (dc_eval dc_c30_1892)

lemma dc_c30_1893: "dc_sub dc_b30 1893"
  by (dc_eval dc_c30_1893)

lemma dc_c30_1894: "dc_sub dc_b30 1894"
  by (dc_eval dc_c30_1894)

lemma dc_c30_1895: "dc_sub dc_b30 1895"
  by (dc_eval dc_c30_1895)

lemma dc_c30_1896: "dc_sub dc_b30 1896"
  by (dc_eval dc_c30_1896)

lemma dc_c30_1897: "dc_sub dc_b30 1897"
  by (dc_eval dc_c30_1897)

lemma dc_c30_1898: "dc_sub dc_b30 1898"
  by (dc_eval dc_c30_1898)

lemma dc_c30_1899: "dc_sub dc_b30 1899"
  by (dc_eval dc_c30_1899)

lemma dc_c30_1900: "dc_sub dc_b30 1900"
  by (dc_eval dc_c30_1900)

lemma dc_c30_1901: "dc_sub dc_b30 1901"
  by (dc_eval dc_c30_1901)

lemma dc_c30_1902: "dc_sub dc_b30 1902"
  by (dc_eval dc_c30_1902)

lemma dc_c30_1903: "dc_sub dc_b30 1903"
  by (dc_eval dc_c30_1903)

lemma upt_c30_118: "[1888..<1904] = [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]"
  by (simp add: upt_rec)

lemma sec_c30_118: "\<forall>j\<in>{16 * 118..<16 * 118 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 118..<16 * 118 + 16}"
  then have "j \<in> set [1888..<1904]" unfolding set_upt by simp
  then have "j \<in> set [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]" unfolding upt_c30_118 .
  then show "dc_sub dc_b30 j" using dc_c30_1888 dc_c30_1889 dc_c30_1890 dc_c30_1891 dc_c30_1892 dc_c30_1893 dc_c30_1894 dc_c30_1895 dc_c30_1896 dc_c30_1897 dc_c30_1898 dc_c30_1899 dc_c30_1900 dc_c30_1901 dc_c30_1902 dc_c30_1903
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
