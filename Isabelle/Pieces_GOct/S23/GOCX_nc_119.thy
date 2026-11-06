theory GOCX_nc_119
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1904: "goc_sub None 1904"
  by (goc_eval goc_nc_1904)

lemma goc_nc_1905: "goc_sub None 1905"
  by (goc_eval goc_nc_1905)

lemma goc_nc_1906: "goc_sub None 1906"
  by (goc_eval goc_nc_1906)

lemma goc_nc_1907: "goc_sub None 1907"
  by (goc_eval goc_nc_1907)

lemma goc_nc_1908: "goc_sub None 1908"
  by (goc_eval goc_nc_1908)

lemma goc_nc_1909: "goc_sub None 1909"
  by (goc_eval goc_nc_1909)

lemma goc_nc_1910: "goc_sub None 1910"
  by (goc_eval goc_nc_1910)

lemma goc_nc_1911: "goc_sub None 1911"
  by (goc_eval goc_nc_1911)

lemma goc_nc_1912: "goc_sub None 1912"
  by (goc_eval goc_nc_1912)

lemma goc_nc_1913: "goc_sub None 1913"
  by (goc_eval goc_nc_1913)

lemma goc_nc_1914: "goc_sub None 1914"
  by (goc_eval goc_nc_1914)

lemma goc_nc_1915: "goc_sub None 1915"
  by (goc_eval goc_nc_1915)

lemma goc_nc_1916: "goc_sub None 1916"
  by (goc_eval goc_nc_1916)

lemma goc_nc_1917: "goc_sub None 1917"
  by (goc_eval goc_nc_1917)

lemma goc_nc_1918: "goc_sub None 1918"
  by (goc_eval goc_nc_1918)

lemma goc_nc_1919: "goc_sub None 1919"
  by (goc_eval goc_nc_1919)

lemma gupt_nc_119: "[1904..<1920] = [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]"
  by (simp add: upt_rec)

lemma gsec_nc_119: "\<forall>j\<in>{16 * 119..<16 * 119 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 119..<16 * 119 + 16}"
  then have "j \<in> set [1904..<1920]" unfolding set_upt by simp
  then have "j \<in> set [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]" unfolding gupt_nc_119 .
  then show "goc_sub None j" using goc_nc_1904 goc_nc_1905 goc_nc_1906 goc_nc_1907 goc_nc_1908 goc_nc_1909 goc_nc_1910 goc_nc_1911 goc_nc_1912 goc_nc_1913 goc_nc_1914 goc_nc_1915 goc_nc_1916 goc_nc_1917 goc_nc_1918 goc_nc_1919
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
