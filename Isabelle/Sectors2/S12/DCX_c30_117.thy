theory DCX_c30_117
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1872: "dc_sub dc_b30 1872"
  by (dc_eval dc_c30_1872)

lemma dc_c30_1873: "dc_sub dc_b30 1873"
  by (dc_eval dc_c30_1873)

lemma dc_c30_1874: "dc_sub dc_b30 1874"
  by (dc_eval dc_c30_1874)

lemma dc_c30_1875: "dc_sub dc_b30 1875"
  by (dc_eval dc_c30_1875)

lemma dc_c30_1876: "dc_sub dc_b30 1876"
  by (dc_eval dc_c30_1876)

lemma dc_c30_1877: "dc_sub dc_b30 1877"
  by (dc_eval dc_c30_1877)

lemma dc_c30_1878: "dc_sub dc_b30 1878"
  by (dc_eval dc_c30_1878)

lemma dc_c30_1879: "dc_sub dc_b30 1879"
  by (dc_eval dc_c30_1879)

lemma dc_c30_1880: "dc_sub dc_b30 1880"
  by (dc_eval dc_c30_1880)

lemma dc_c30_1881: "dc_sub dc_b30 1881"
  by (dc_eval dc_c30_1881)

lemma dc_c30_1882: "dc_sub dc_b30 1882"
  by (dc_eval dc_c30_1882)

lemma dc_c30_1883: "dc_sub dc_b30 1883"
  by (dc_eval dc_c30_1883)

lemma dc_c30_1884: "dc_sub dc_b30 1884"
  by (dc_eval dc_c30_1884)

lemma dc_c30_1885: "dc_sub dc_b30 1885"
  by (dc_eval dc_c30_1885)

lemma dc_c30_1886: "dc_sub dc_b30 1886"
  by (dc_eval dc_c30_1886)

lemma dc_c30_1887: "dc_sub dc_b30 1887"
  by (dc_eval dc_c30_1887)

lemma upt_c30_117: "[1872..<1888] = [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]"
  by (simp add: upt_rec)

lemma sec_c30_117: "\<forall>j\<in>{16 * 117..<16 * 117 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 117..<16 * 117 + 16}"
  then have "j \<in> set [1872..<1888]" unfolding set_upt by simp
  then have "j \<in> set [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]" unfolding upt_c30_117 .
  then show "dc_sub dc_b30 j" using dc_c30_1872 dc_c30_1873 dc_c30_1874 dc_c30_1875 dc_c30_1876 dc_c30_1877 dc_c30_1878 dc_c30_1879 dc_c30_1880 dc_c30_1881 dc_c30_1882 dc_c30_1883 dc_c30_1884 dc_c30_1885 dc_c30_1886 dc_c30_1887
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
