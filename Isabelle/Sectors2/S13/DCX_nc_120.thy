theory DCX_nc_120
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1920: "dc_sub None 1920"
  by (dc_eval dc_nc_1920)

lemma dc_nc_1921: "dc_sub None 1921"
  by (dc_eval dc_nc_1921)

lemma dc_nc_1922: "dc_sub None 1922"
  by (dc_eval dc_nc_1922)

lemma dc_nc_1923: "dc_sub None 1923"
  by (dc_eval dc_nc_1923)

lemma dc_nc_1924: "dc_sub None 1924"
  by (dc_eval dc_nc_1924)

lemma dc_nc_1925: "dc_sub None 1925"
  by (dc_eval dc_nc_1925)

lemma dc_nc_1926: "dc_sub None 1926"
  by (dc_eval dc_nc_1926)

lemma dc_nc_1927: "dc_sub None 1927"
  by (dc_eval dc_nc_1927)

lemma dc_nc_1928: "dc_sub None 1928"
  by (dc_eval dc_nc_1928)

lemma dc_nc_1929: "dc_sub None 1929"
  by (dc_eval dc_nc_1929)

lemma dc_nc_1930: "dc_sub None 1930"
  by (dc_eval dc_nc_1930)

lemma dc_nc_1931: "dc_sub None 1931"
  by (dc_eval dc_nc_1931)

lemma dc_nc_1932: "dc_sub None 1932"
  by (dc_eval dc_nc_1932)

lemma dc_nc_1933: "dc_sub None 1933"
  by (dc_eval dc_nc_1933)

lemma dc_nc_1934: "dc_sub None 1934"
  by (dc_eval dc_nc_1934)

lemma dc_nc_1935: "dc_sub None 1935"
  by (dc_eval dc_nc_1935)

lemma upt_nc_120: "[1920..<1936] = [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]"
  by (simp add: upt_rec)

lemma sec_nc_120: "\<forall>j\<in>{16 * 120..<16 * 120 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 120..<16 * 120 + 16}"
  then have "j \<in> set [1920..<1936]" unfolding set_upt by simp
  then have "j \<in> set [1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935]" unfolding upt_nc_120 .
  then show "dc_sub None j" using dc_nc_1920 dc_nc_1921 dc_nc_1922 dc_nc_1923 dc_nc_1924 dc_nc_1925 dc_nc_1926 dc_nc_1927 dc_nc_1928 dc_nc_1929 dc_nc_1930 dc_nc_1931 dc_nc_1932 dc_nc_1933 dc_nc_1934 dc_nc_1935
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
