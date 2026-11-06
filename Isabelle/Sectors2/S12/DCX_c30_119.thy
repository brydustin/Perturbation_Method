theory DCX_c30_119
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1904: "dc_sub dc_b30 1904"
  by (dc_eval dc_c30_1904)

lemma dc_c30_1905: "dc_sub dc_b30 1905"
  by (dc_eval dc_c30_1905)

lemma dc_c30_1906: "dc_sub dc_b30 1906"
  by (dc_eval dc_c30_1906)

lemma dc_c30_1907: "dc_sub dc_b30 1907"
  by (dc_eval dc_c30_1907)

lemma dc_c30_1908: "dc_sub dc_b30 1908"
  by (dc_eval dc_c30_1908)

lemma dc_c30_1909: "dc_sub dc_b30 1909"
  by (dc_eval dc_c30_1909)

lemma dc_c30_1910: "dc_sub dc_b30 1910"
  by (dc_eval dc_c30_1910)

lemma dc_c30_1911: "dc_sub dc_b30 1911"
  by (dc_eval dc_c30_1911)

lemma dc_c30_1912: "dc_sub dc_b30 1912"
  by (dc_eval dc_c30_1912)

lemma dc_c30_1913: "dc_sub dc_b30 1913"
  by (dc_eval dc_c30_1913)

lemma dc_c30_1914: "dc_sub dc_b30 1914"
  by (dc_eval dc_c30_1914)

lemma dc_c30_1915: "dc_sub dc_b30 1915"
  by (dc_eval dc_c30_1915)

lemma dc_c30_1916: "dc_sub dc_b30 1916"
  by (dc_eval dc_c30_1916)

lemma dc_c30_1917: "dc_sub dc_b30 1917"
  by (dc_eval dc_c30_1917)

lemma dc_c30_1918: "dc_sub dc_b30 1918"
  by (dc_eval dc_c30_1918)

lemma dc_c30_1919: "dc_sub dc_b30 1919"
  by (dc_eval dc_c30_1919)

lemma upt_c30_119: "[1904..<1920] = [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]"
  by (simp add: upt_rec)

lemma sec_c30_119: "\<forall>j\<in>{16 * 119..<16 * 119 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 119..<16 * 119 + 16}"
  then have "j \<in> set [1904..<1920]" unfolding set_upt by simp
  then have "j \<in> set [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]" unfolding upt_c30_119 .
  then show "dc_sub dc_b30 j" using dc_c30_1904 dc_c30_1905 dc_c30_1906 dc_c30_1907 dc_c30_1908 dc_c30_1909 dc_c30_1910 dc_c30_1911 dc_c30_1912 dc_c30_1913 dc_c30_1914 dc_c30_1915 dc_c30_1916 dc_c30_1917 dc_c30_1918 dc_c30_1919
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
