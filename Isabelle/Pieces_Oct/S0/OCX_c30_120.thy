theory OCX_c30_120
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1920: "oc_sub oc_b30 1920"
  by (oc_eval oc_c30_1920)

lemma oc_c30_1921: "oc_sub oc_b30 1921"
  by (oc_eval oc_c30_1921)

lemma oc_c30_1922: "oc_sub oc_b30 1922"
  by (oc_eval oc_c30_1922)

lemma oc_c30_1923: "oc_sub oc_b30 1923"
  by (oc_eval oc_c30_1923)

lemma oc_c30_1924: "oc_sub oc_b30 1924"
  by (oc_eval oc_c30_1924)

lemma oc_c30_1925: "oc_sub oc_b30 1925"
  by (oc_eval oc_c30_1925)

lemma oc_c30_1926: "oc_sub oc_b30 1926"
  by (oc_eval oc_c30_1926)

lemma oc_c30_1927: "oc_sub oc_b30 1927"
  by (oc_eval oc_c30_1927)

lemma oc_c30_1928: "oc_sub oc_b30 1928"
  by (oc_eval oc_c30_1928)

lemma oc_c30_1929: "oc_sub oc_b30 1929"
  by (oc_eval oc_c30_1929)

lemma oc_c30_1930: "oc_sub oc_b30 1930"
  by (oc_eval oc_c30_1930)

lemma oc_c30_1931: "oc_sub oc_b30 1931"
  by (oc_eval oc_c30_1931)

lemma oc_c30_1932: "oc_sub oc_b30 1932"
  by (oc_eval oc_c30_1932)

lemma oc_c30_1933: "oc_sub oc_b30 1933"
  by (oc_eval oc_c30_1933)

lemma oc_c30_1934: "oc_sub oc_b30 1934"
  by (oc_eval oc_c30_1934)

lemma oc_c30_1935: "oc_sub oc_b30 1935"
  by (oc_eval oc_c30_1935)

lemma upt_c30_120: "[1920..<1936] = [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]"
  by (simp add: upt_rec)

lemma sec_c30_120: "\<forall>j\<in>{16 * 120..<16 * 120 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 120..<16 * 120 + 16}"
  then have "j \<in> set [1920..<1936]" unfolding set_upt by simp
  then have "j \<in> set [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]" unfolding upt_c30_120 .
  then show "oc_sub oc_b30 j" using oc_c30_1920 oc_c30_1921 oc_c30_1922 oc_c30_1923 oc_c30_1924 oc_c30_1925 oc_c30_1926 oc_c30_1927 oc_c30_1928 oc_c30_1929 oc_c30_1930 oc_c30_1931 oc_c30_1932 oc_c30_1933 oc_c30_1934 oc_c30_1935
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
