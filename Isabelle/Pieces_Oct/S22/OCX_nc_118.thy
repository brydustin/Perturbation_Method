theory OCX_nc_118
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1888: "oc_sub None 1888"
  by (oc_eval oc_nc_1888)

lemma oc_nc_1889: "oc_sub None 1889"
  by (oc_eval oc_nc_1889)

lemma oc_nc_1890: "oc_sub None 1890"
  by (oc_eval oc_nc_1890)

lemma oc_nc_1891: "oc_sub None 1891"
  by (oc_eval oc_nc_1891)

lemma oc_nc_1892: "oc_sub None 1892"
  by (oc_eval oc_nc_1892)

lemma oc_nc_1893: "oc_sub None 1893"
  by (oc_eval oc_nc_1893)

lemma oc_nc_1894: "oc_sub None 1894"
  by (oc_eval oc_nc_1894)

lemma oc_nc_1895: "oc_sub None 1895"
  by (oc_eval oc_nc_1895)

lemma oc_nc_1896: "oc_sub None 1896"
  by (oc_eval oc_nc_1896)

lemma oc_nc_1897: "oc_sub None 1897"
  by (oc_eval oc_nc_1897)

lemma oc_nc_1898: "oc_sub None 1898"
  by (oc_eval oc_nc_1898)

lemma oc_nc_1899: "oc_sub None 1899"
  by (oc_eval oc_nc_1899)

lemma oc_nc_1900: "oc_sub None 1900"
  by (oc_eval oc_nc_1900)

lemma oc_nc_1901: "oc_sub None 1901"
  by (oc_eval oc_nc_1901)

lemma oc_nc_1902: "oc_sub None 1902"
  by (oc_eval oc_nc_1902)

lemma oc_nc_1903: "oc_sub None 1903"
  by (oc_eval oc_nc_1903)

lemma upt_nc_118: "[1888..<1904] = [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]"
  by (simp add: upt_rec)

lemma sec_nc_118: "\<forall>j\<in>{16 * 118..<16 * 118 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 118..<16 * 118 + 16}"
  then have "j \<in> set [1888..<1904]" unfolding set_upt by simp
  then have "j \<in> set [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]" unfolding upt_nc_118 .
  then show "oc_sub None j" using oc_nc_1888 oc_nc_1889 oc_nc_1890 oc_nc_1891 oc_nc_1892 oc_nc_1893 oc_nc_1894 oc_nc_1895 oc_nc_1896 oc_nc_1897 oc_nc_1898 oc_nc_1899 oc_nc_1900 oc_nc_1901 oc_nc_1902 oc_nc_1903
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
