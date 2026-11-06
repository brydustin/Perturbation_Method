theory GOCX_nc_120
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1920: "goc_sub None 1920"
  by (goc_eval goc_nc_1920)

lemma goc_nc_1921: "goc_sub None 1921"
  by (goc_eval goc_nc_1921)

lemma goc_nc_1922: "goc_sub None 1922"
  by (goc_eval goc_nc_1922)

lemma goc_nc_1923: "goc_sub None 1923"
  by (goc_eval goc_nc_1923)

lemma goc_nc_1924: "goc_sub None 1924"
  by (goc_eval goc_nc_1924)

lemma goc_nc_1925: "goc_sub None 1925"
  by (goc_eval goc_nc_1925)

lemma goc_nc_1926: "goc_sub None 1926"
  by (goc_eval goc_nc_1926)

lemma goc_nc_1927: "goc_sub None 1927"
  by (goc_eval goc_nc_1927)

lemma goc_nc_1928: "goc_sub None 1928"
  by (goc_eval goc_nc_1928)

lemma goc_nc_1929: "goc_sub None 1929"
  by (goc_eval goc_nc_1929)

lemma goc_nc_1930: "goc_sub None 1930"
  by (goc_eval goc_nc_1930)

lemma goc_nc_1931: "goc_sub None 1931"
  by (goc_eval goc_nc_1931)

lemma goc_nc_1932: "goc_sub None 1932"
  by (goc_eval goc_nc_1932)

lemma goc_nc_1933: "goc_sub None 1933"
  by (goc_eval goc_nc_1933)

lemma goc_nc_1934: "goc_sub None 1934"
  by (goc_eval goc_nc_1934)

lemma goc_nc_1935: "goc_sub None 1935"
  by (goc_eval goc_nc_1935)

lemma gupt_nc_120: "[1920..<1936] = [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]"
  by (simp add: upt_rec)

lemma gsec_nc_120: "\<forall>j\<in>{16 * 120..<16 * 120 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 120..<16 * 120 + 16}"
  then have "j \<in> set [1920..<1936]" unfolding set_upt by simp
  then have "j \<in> set [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]" unfolding gupt_nc_120 .
  then show "goc_sub None j" using goc_nc_1920 goc_nc_1921 goc_nc_1922 goc_nc_1923 goc_nc_1924 goc_nc_1925 goc_nc_1926 goc_nc_1927 goc_nc_1928 goc_nc_1929 goc_nc_1930 goc_nc_1931 goc_nc_1932 goc_nc_1933 goc_nc_1934 goc_nc_1935
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
