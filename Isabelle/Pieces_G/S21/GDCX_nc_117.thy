theory GDCX_nc_117
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1872: "gdc_sub None 1872"
  by (gdc_eval gdc_nc_1872)

lemma gdc_nc_1873: "gdc_sub None 1873"
  by (gdc_eval gdc_nc_1873)

lemma gdc_nc_1874: "gdc_sub None 1874"
  by (gdc_eval gdc_nc_1874)

lemma gdc_nc_1875: "gdc_sub None 1875"
  by (gdc_eval gdc_nc_1875)

lemma gdc_nc_1876: "gdc_sub None 1876"
  by (gdc_eval gdc_nc_1876)

lemma gdc_nc_1877: "gdc_sub None 1877"
  by (gdc_eval gdc_nc_1877)

lemma gdc_nc_1878: "gdc_sub None 1878"
  by (gdc_eval gdc_nc_1878)

lemma gdc_nc_1879: "gdc_sub None 1879"
  by (gdc_eval gdc_nc_1879)

lemma gdc_nc_1880: "gdc_sub None 1880"
  by (gdc_eval gdc_nc_1880)

lemma gdc_nc_1881: "gdc_sub None 1881"
  by (gdc_eval gdc_nc_1881)

lemma gdc_nc_1882: "gdc_sub None 1882"
  by (gdc_eval gdc_nc_1882)

lemma gdc_nc_1883: "gdc_sub None 1883"
  by (gdc_eval gdc_nc_1883)

lemma gdc_nc_1884: "gdc_sub None 1884"
  by (gdc_eval gdc_nc_1884)

lemma gdc_nc_1885: "gdc_sub None 1885"
  by (gdc_eval gdc_nc_1885)

lemma gdc_nc_1886: "gdc_sub None 1886"
  by (gdc_eval gdc_nc_1886)

lemma gdc_nc_1887: "gdc_sub None 1887"
  by (gdc_eval gdc_nc_1887)

lemma gupt_nc_117: "[1872..<1888] = [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]"
  by (simp add: upt_rec)

lemma gsec_nc_117: "\<forall>j\<in>{16 * 117..<16 * 117 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 117..<16 * 117 + 16}"
  then have "j \<in> set [1872..<1888]" unfolding set_upt by simp
  then have "j \<in> set [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]" unfolding gupt_nc_117 .
  then show "gdc_sub None j" using gdc_nc_1872 gdc_nc_1873 gdc_nc_1874 gdc_nc_1875 gdc_nc_1876 gdc_nc_1877 gdc_nc_1878 gdc_nc_1879 gdc_nc_1880 gdc_nc_1881 gdc_nc_1882 gdc_nc_1883 gdc_nc_1884 gdc_nc_1885 gdc_nc_1886 gdc_nc_1887
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
