theory OCX_nc_120
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1920: "oc_sub None 1920"
  by (oc_eval oc_nc_1920)

lemma oc_nc_1921: "oc_sub None 1921"
  by (oc_eval oc_nc_1921)

lemma oc_nc_1922: "oc_sub None 1922"
  by (oc_eval oc_nc_1922)

lemma oc_nc_1923: "oc_sub None 1923"
  by (oc_eval oc_nc_1923)

lemma oc_nc_1924: "oc_sub None 1924"
  by (oc_eval oc_nc_1924)

lemma oc_nc_1925: "oc_sub None 1925"
  by (oc_eval oc_nc_1925)

lemma oc_nc_1926: "oc_sub None 1926"
  by (oc_eval oc_nc_1926)

lemma oc_nc_1927: "oc_sub None 1927"
  by (oc_eval oc_nc_1927)

lemma oc_nc_1928: "oc_sub None 1928"
  by (oc_eval oc_nc_1928)

lemma oc_nc_1929: "oc_sub None 1929"
  by (oc_eval oc_nc_1929)

lemma oc_nc_1930: "oc_sub None 1930"
  by (oc_eval oc_nc_1930)

lemma oc_nc_1931: "oc_sub None 1931"
  by (oc_eval oc_nc_1931)

lemma oc_nc_1932: "oc_sub None 1932"
  by (oc_eval oc_nc_1932)

lemma oc_nc_1933: "oc_sub None 1933"
  by (oc_eval oc_nc_1933)

lemma oc_nc_1934: "oc_sub None 1934"
  by (oc_eval oc_nc_1934)

lemma oc_nc_1935: "oc_sub None 1935"
  by (oc_eval oc_nc_1935)

lemma upt_nc_120: "[1920..<1936] = [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]"
  by (simp add: upt_rec)

lemma sec_nc_120: "\<forall>j\<in>{16 * 120..<16 * 120 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 120..<16 * 120 + 16}"
  then have "j \<in> set [1920..<1936]" unfolding set_upt by simp
  then have "j \<in> set [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]" unfolding upt_nc_120 .
  then show "oc_sub None j" using oc_nc_1920 oc_nc_1921 oc_nc_1922 oc_nc_1923 oc_nc_1924 oc_nc_1925 oc_nc_1926 oc_nc_1927 oc_nc_1928 oc_nc_1929 oc_nc_1930 oc_nc_1931 oc_nc_1932 oc_nc_1933 oc_nc_1934 oc_nc_1935
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
