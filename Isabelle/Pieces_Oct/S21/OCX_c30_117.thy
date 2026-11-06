theory OCX_c30_117
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1872: "oc_sub oc_b30 1872"
  by (oc_eval oc_c30_1872)

lemma oc_c30_1873: "oc_sub oc_b30 1873"
  by (oc_eval oc_c30_1873)

lemma oc_c30_1874: "oc_sub oc_b30 1874"
  by (oc_eval oc_c30_1874)

lemma oc_c30_1875: "oc_sub oc_b30 1875"
  by (oc_eval oc_c30_1875)

lemma oc_c30_1876: "oc_sub oc_b30 1876"
  by (oc_eval oc_c30_1876)

lemma oc_c30_1877: "oc_sub oc_b30 1877"
  by (oc_eval oc_c30_1877)

lemma oc_c30_1878: "oc_sub oc_b30 1878"
  by (oc_eval oc_c30_1878)

lemma oc_c30_1879: "oc_sub oc_b30 1879"
  by (oc_eval oc_c30_1879)

lemma oc_c30_1880: "oc_sub oc_b30 1880"
  by (oc_eval oc_c30_1880)

lemma oc_c30_1881: "oc_sub oc_b30 1881"
  by (oc_eval oc_c30_1881)

lemma oc_c30_1882: "oc_sub oc_b30 1882"
  by (oc_eval oc_c30_1882)

lemma oc_c30_1883: "oc_sub oc_b30 1883"
  by (oc_eval oc_c30_1883)

lemma oc_c30_1884: "oc_sub oc_b30 1884"
  by (oc_eval oc_c30_1884)

lemma oc_c30_1885: "oc_sub oc_b30 1885"
  by (oc_eval oc_c30_1885)

lemma oc_c30_1886: "oc_sub oc_b30 1886"
  by (oc_eval oc_c30_1886)

lemma oc_c30_1887: "oc_sub oc_b30 1887"
  by (oc_eval oc_c30_1887)

lemma upt_c30_117: "[1872..<1888] = [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]"
  by (simp add: upt_rec)

lemma sec_c30_117: "\<forall>j\<in>{16 * 117..<16 * 117 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 117..<16 * 117 + 16}"
  then have "j \<in> set [1872..<1888]" unfolding set_upt by simp
  then have "j \<in> set [1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887]" unfolding upt_c30_117 .
  then show "oc_sub oc_b30 j" using oc_c30_1872 oc_c30_1873 oc_c30_1874 oc_c30_1875 oc_c30_1876 oc_c30_1877 oc_c30_1878 oc_c30_1879 oc_c30_1880 oc_c30_1881 oc_c30_1882 oc_c30_1883 oc_c30_1884 oc_c30_1885 oc_c30_1886 oc_c30_1887
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
