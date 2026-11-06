theory GDCX_nc_120
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1920: "gdc_sub None 1920"
  by (gdc_eval gdc_nc_1920)

lemma gdc_nc_1921: "gdc_sub None 1921"
  by (gdc_eval gdc_nc_1921)

lemma gdc_nc_1922: "gdc_sub None 1922"
  by (gdc_eval gdc_nc_1922)

lemma gdc_nc_1923: "gdc_sub None 1923"
  by (gdc_eval gdc_nc_1923)

lemma gdc_nc_1924: "gdc_sub None 1924"
  by (gdc_eval gdc_nc_1924)

lemma gdc_nc_1925: "gdc_sub None 1925"
  by (gdc_eval gdc_nc_1925)

lemma gdc_nc_1926: "gdc_sub None 1926"
  by (gdc_eval gdc_nc_1926)

lemma gdc_nc_1927: "gdc_sub None 1927"
  by (gdc_eval gdc_nc_1927)

lemma gdc_nc_1928: "gdc_sub None 1928"
  by (gdc_eval gdc_nc_1928)

lemma gdc_nc_1929: "gdc_sub None 1929"
  by (gdc_eval gdc_nc_1929)

lemma gdc_nc_1930: "gdc_sub None 1930"
  by (gdc_eval gdc_nc_1930)

lemma gdc_nc_1931: "gdc_sub None 1931"
  by (gdc_eval gdc_nc_1931)

lemma gdc_nc_1932: "gdc_sub None 1932"
  by (gdc_eval gdc_nc_1932)

lemma gdc_nc_1933: "gdc_sub None 1933"
  by (gdc_eval gdc_nc_1933)

lemma gdc_nc_1934: "gdc_sub None 1934"
  by (gdc_eval gdc_nc_1934)

lemma gdc_nc_1935: "gdc_sub None 1935"
  by (gdc_eval gdc_nc_1935)

lemma gupt_nc_120: "[1920..<1936] = [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]"
  by (simp add: upt_rec)

lemma gsec_nc_120: "\<forall>j\<in>{16 * 120..<16 * 120 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 120..<16 * 120 + 16}"
  then have "j \<in> set [1920..<1936]" unfolding set_upt by simp
  then have "j \<in> set [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]" unfolding gupt_nc_120 .
  then show "gdc_sub None j" using gdc_nc_1920 gdc_nc_1921 gdc_nc_1922 gdc_nc_1923 gdc_nc_1924 gdc_nc_1925 gdc_nc_1926 gdc_nc_1927 gdc_nc_1928 gdc_nc_1929 gdc_nc_1930 gdc_nc_1931 gdc_nc_1932 gdc_nc_1933 gdc_nc_1934 gdc_nc_1935
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
