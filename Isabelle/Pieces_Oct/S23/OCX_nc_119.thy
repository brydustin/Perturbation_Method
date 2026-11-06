theory OCX_nc_119
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1904: "oc_sub None 1904"
  by (oc_eval oc_nc_1904)

lemma oc_nc_1905: "oc_sub None 1905"
  by (oc_eval oc_nc_1905)

lemma oc_nc_1906: "oc_sub None 1906"
  by (oc_eval oc_nc_1906)

lemma oc_nc_1907: "oc_sub None 1907"
  by (oc_eval oc_nc_1907)

lemma oc_nc_1908: "oc_sub None 1908"
  by (oc_eval oc_nc_1908)

lemma oc_nc_1909: "oc_sub None 1909"
  by (oc_eval oc_nc_1909)

lemma oc_nc_1910: "oc_sub None 1910"
  by (oc_eval oc_nc_1910)

lemma oc_nc_1911: "oc_sub None 1911"
  by (oc_eval oc_nc_1911)

lemma oc_nc_1912: "oc_sub None 1912"
  by (oc_eval oc_nc_1912)

lemma oc_nc_1913: "oc_sub None 1913"
  by (oc_eval oc_nc_1913)

lemma oc_nc_1914: "oc_sub None 1914"
  by (oc_eval oc_nc_1914)

lemma oc_nc_1915: "oc_sub None 1915"
  by (oc_eval oc_nc_1915)

lemma oc_nc_1916: "oc_sub None 1916"
  by (oc_eval oc_nc_1916)

lemma oc_nc_1917: "oc_sub None 1917"
  by (oc_eval oc_nc_1917)

lemma oc_nc_1918: "oc_sub None 1918"
  by (oc_eval oc_nc_1918)

lemma oc_nc_1919: "oc_sub None 1919"
  by (oc_eval oc_nc_1919)

lemma upt_nc_119: "[1904..<1920] = [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]"
  by (simp add: upt_rec)

lemma sec_nc_119: "\<forall>j\<in>{16 * 119..<16 * 119 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 119..<16 * 119 + 16}"
  then have "j \<in> set [1904..<1920]" unfolding set_upt by simp
  then have "j \<in> set [1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919]" unfolding upt_nc_119 .
  then show "oc_sub None j" using oc_nc_1904 oc_nc_1905 oc_nc_1906 oc_nc_1907 oc_nc_1908 oc_nc_1909 oc_nc_1910 oc_nc_1911 oc_nc_1912 oc_nc_1913 oc_nc_1914 oc_nc_1915 oc_nc_1916 oc_nc_1917 oc_nc_1918 oc_nc_1919
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
