theory GOCX_nc_117
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1872: "goc_sub None 1872"
  by (goc_eval goc_nc_1872)

lemma goc_nc_1873: "goc_sub None 1873"
  by (goc_eval goc_nc_1873)

lemma goc_nc_1874: "goc_sub None 1874"
  by (goc_eval goc_nc_1874)

lemma goc_nc_1875: "goc_sub None 1875"
  by (goc_eval goc_nc_1875)

lemma goc_nc_1876: "goc_sub None 1876"
  by (goc_eval goc_nc_1876)

lemma goc_nc_1877: "goc_sub None 1877"
  by (goc_eval goc_nc_1877)

lemma goc_nc_1878: "goc_sub None 1878"
  by (goc_eval goc_nc_1878)

lemma goc_nc_1879: "goc_sub None 1879"
  by (goc_eval goc_nc_1879)

lemma goc_nc_1880: "goc_sub None 1880"
  by (goc_eval goc_nc_1880)

lemma goc_nc_1881: "goc_sub None 1881"
  by (goc_eval goc_nc_1881)

lemma goc_nc_1882: "goc_sub None 1882"
  by (goc_eval goc_nc_1882)

lemma goc_nc_1883: "goc_sub None 1883"
  by (goc_eval goc_nc_1883)

lemma goc_nc_1884: "goc_sub None 1884"
  by (goc_eval goc_nc_1884)

lemma goc_nc_1885: "goc_sub None 1885"
  by (goc_eval goc_nc_1885)

lemma goc_nc_1886: "goc_sub None 1886"
  by (goc_eval goc_nc_1886)

lemma goc_nc_1887: "goc_sub None 1887"
  by (goc_eval goc_nc_1887)

lemma gupt_nc_117: "[1872..<1888] = [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]"
  by (simp add: upt_rec)

lemma gsec_nc_117: "\<forall>j\<in>{16 * 117..<16 * 117 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 117..<16 * 117 + 16}"
  then have "j \<in> set [1872..<1888]" unfolding set_upt by simp
  then have "j \<in> set [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]" unfolding gupt_nc_117 .
  then show "goc_sub None j" using goc_nc_1872 goc_nc_1873 goc_nc_1874 goc_nc_1875 goc_nc_1876 goc_nc_1877 goc_nc_1878 goc_nc_1879 goc_nc_1880 goc_nc_1881 goc_nc_1882 goc_nc_1883 goc_nc_1884 goc_nc_1885 goc_nc_1886 goc_nc_1887
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
