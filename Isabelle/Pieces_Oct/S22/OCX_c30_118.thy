theory OCX_c30_118
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1888: "oc_sub oc_b30 1888"
  by (oc_eval oc_c30_1888)

lemma oc_c30_1889: "oc_sub oc_b30 1889"
  by (oc_eval oc_c30_1889)

lemma oc_c30_1890: "oc_sub oc_b30 1890"
  by (oc_eval oc_c30_1890)

lemma oc_c30_1891: "oc_sub oc_b30 1891"
  by (oc_eval oc_c30_1891)

lemma oc_c30_1892: "oc_sub oc_b30 1892"
  by (oc_eval oc_c30_1892)

lemma oc_c30_1893: "oc_sub oc_b30 1893"
  by (oc_eval oc_c30_1893)

lemma oc_c30_1894: "oc_sub oc_b30 1894"
  by (oc_eval oc_c30_1894)

lemma oc_c30_1895: "oc_sub oc_b30 1895"
  by (oc_eval oc_c30_1895)

lemma oc_c30_1896: "oc_sub oc_b30 1896"
  by (oc_eval oc_c30_1896)

lemma oc_c30_1897: "oc_sub oc_b30 1897"
  by (oc_eval oc_c30_1897)

lemma oc_c30_1898: "oc_sub oc_b30 1898"
  by (oc_eval oc_c30_1898)

lemma oc_c30_1899: "oc_sub oc_b30 1899"
  by (oc_eval oc_c30_1899)

lemma oc_c30_1900: "oc_sub oc_b30 1900"
  by (oc_eval oc_c30_1900)

lemma oc_c30_1901: "oc_sub oc_b30 1901"
  by (oc_eval oc_c30_1901)

lemma oc_c30_1902: "oc_sub oc_b30 1902"
  by (oc_eval oc_c30_1902)

lemma oc_c30_1903: "oc_sub oc_b30 1903"
  by (oc_eval oc_c30_1903)

lemma upt_c30_118: "[1888..<1904] = [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]"
  by (simp add: upt_rec)

lemma sec_c30_118: "\<forall>j\<in>{16 * 118..<16 * 118 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 118..<16 * 118 + 16}"
  then have "j \<in> set [1888..<1904]" unfolding set_upt by simp
  then have "j \<in> set [1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903]" unfolding upt_c30_118 .
  then show "oc_sub oc_b30 j" using oc_c30_1888 oc_c30_1889 oc_c30_1890 oc_c30_1891 oc_c30_1892 oc_c30_1893 oc_c30_1894 oc_c30_1895 oc_c30_1896 oc_c30_1897 oc_c30_1898 oc_c30_1899 oc_c30_1900 oc_c30_1901 oc_c30_1902 oc_c30_1903
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
