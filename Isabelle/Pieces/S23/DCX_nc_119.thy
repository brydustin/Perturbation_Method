theory DCX_nc_119
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1904: "dc_sub None 1904"
  by (dc_eval dc_nc_1904)

lemma dc_nc_1905: "dc_sub None 1905"
  by (dc_eval dc_nc_1905)

lemma dc_nc_1906: "dc_sub None 1906"
  by (dc_eval dc_nc_1906)

lemma dc_nc_1907: "dc_sub None 1907"
  by (dc_eval dc_nc_1907)

lemma dc_nc_1908: "dc_sub None 1908"
  by (dc_eval dc_nc_1908)

lemma dc_nc_1909: "dc_sub None 1909"
  by (dc_eval dc_nc_1909)

lemma dc_nc_1910: "dc_sub None 1910"
  by (dc_eval dc_nc_1910)

lemma dc_nc_1911: "dc_sub None 1911"
  by (dc_eval dc_nc_1911)

lemma dc_nc_1912: "dc_sub None 1912"
  by (dc_eval dc_nc_1912)

lemma dc_nc_1913: "dc_sub None 1913"
  by (dc_eval dc_nc_1913)

lemma dc_nc_1914: "dc_sub None 1914"
  by (dc_eval dc_nc_1914)

lemma dc_nc_1915: "dc_sub None 1915"
  by (dc_eval dc_nc_1915)

lemma dc_nc_1916: "dc_sub None 1916"
  by (dc_eval dc_nc_1916)

lemma dc_nc_1917: "dc_sub None 1917"
  by (dc_eval dc_nc_1917)

lemma dc_nc_1918: "dc_sub None 1918"
  by (dc_eval dc_nc_1918)

lemma dc_nc_1919: "dc_sub None 1919"
  by (dc_eval dc_nc_1919)

lemma upt_nc_119: "[1904..<1920] = [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]"
  by (simp add: upt_rec)

lemma sec_nc_119: "\<forall>j\<in>{16 * 119..<16 * 119 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 119..<16 * 119 + 16}"
  then have "j \<in> set [1904..<1920]" unfolding set_upt by simp
  then have "j \<in> set [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]" unfolding upt_nc_119 .
  then show "dc_sub None j" using dc_nc_1904 dc_nc_1905 dc_nc_1906 dc_nc_1907 dc_nc_1908 dc_nc_1909 dc_nc_1910 dc_nc_1911 dc_nc_1912 dc_nc_1913 dc_nc_1914 dc_nc_1915 dc_nc_1916 dc_nc_1917 dc_nc_1918 dc_nc_1919
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
