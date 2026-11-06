theory GDCX_nc_119
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1904: "gdc_sub None 1904"
  by (gdc_eval gdc_nc_1904)

lemma gdc_nc_1905: "gdc_sub None 1905"
  by (gdc_eval gdc_nc_1905)

lemma gdc_nc_1906: "gdc_sub None 1906"
  by (gdc_eval gdc_nc_1906)

lemma gdc_nc_1907: "gdc_sub None 1907"
  by (gdc_eval gdc_nc_1907)

lemma gdc_nc_1908: "gdc_sub None 1908"
  by (gdc_eval gdc_nc_1908)

lemma gdc_nc_1909: "gdc_sub None 1909"
  by (gdc_eval gdc_nc_1909)

lemma gdc_nc_1910: "gdc_sub None 1910"
  by (gdc_eval gdc_nc_1910)

lemma gdc_nc_1911: "gdc_sub None 1911"
  by (gdc_eval gdc_nc_1911)

lemma gdc_nc_1912: "gdc_sub None 1912"
  by (gdc_eval gdc_nc_1912)

lemma gdc_nc_1913: "gdc_sub None 1913"
  by (gdc_eval gdc_nc_1913)

lemma gdc_nc_1914: "gdc_sub None 1914"
  by (gdc_eval gdc_nc_1914)

lemma gdc_nc_1915: "gdc_sub None 1915"
  by (gdc_eval gdc_nc_1915)

lemma gdc_nc_1916: "gdc_sub None 1916"
  by (gdc_eval gdc_nc_1916)

lemma gdc_nc_1917: "gdc_sub None 1917"
  by (gdc_eval gdc_nc_1917)

lemma gdc_nc_1918: "gdc_sub None 1918"
  by (gdc_eval gdc_nc_1918)

lemma gdc_nc_1919: "gdc_sub None 1919"
  by (gdc_eval gdc_nc_1919)

lemma gupt_nc_119: "[1904..<1920] = [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]"
  by (simp add: upt_rec)

lemma gsec_nc_119: "\<forall>j\<in>{16 * 119..<16 * 119 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 119..<16 * 119 + 16}"
  then have "j \<in> set [1904..<1920]" unfolding set_upt by simp
  then have "j \<in> set [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]" unfolding gupt_nc_119 .
  then show "gdc_sub None j" using gdc_nc_1904 gdc_nc_1905 gdc_nc_1906 gdc_nc_1907 gdc_nc_1908 gdc_nc_1909 gdc_nc_1910 gdc_nc_1911 gdc_nc_1912 gdc_nc_1913 gdc_nc_1914 gdc_nc_1915 gdc_nc_1916 gdc_nc_1917 gdc_nc_1918 gdc_nc_1919
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
