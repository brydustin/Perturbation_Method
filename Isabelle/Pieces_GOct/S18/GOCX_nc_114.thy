theory GOCX_nc_114
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1824: "goc_sub None 1824"
  by (goc_eval goc_nc_1824)

lemma goc_nc_1825: "goc_sub None 1825"
  by (goc_eval goc_nc_1825)

lemma goc_nc_1826: "goc_sub None 1826"
  by (goc_eval goc_nc_1826)

lemma goc_nc_1827: "goc_sub None 1827"
  by (goc_eval goc_nc_1827)

lemma goc_nc_1828: "goc_sub None 1828"
  by (goc_eval goc_nc_1828)

lemma goc_nc_1829: "goc_sub None 1829"
  by (goc_eval goc_nc_1829)

lemma goc_nc_1830: "goc_sub None 1830"
  by (goc_eval goc_nc_1830)

lemma goc_nc_1831: "goc_sub None 1831"
  by (goc_eval goc_nc_1831)

lemma goc_nc_1832: "goc_sub None 1832"
  by (goc_eval goc_nc_1832)

lemma goc_nc_1833: "goc_sub None 1833"
  by (goc_eval goc_nc_1833)

lemma goc_nc_1834: "goc_sub None 1834"
  by (goc_eval goc_nc_1834)

lemma goc_nc_1835: "goc_sub None 1835"
  by (goc_eval goc_nc_1835)

lemma goc_nc_1836: "goc_sub None 1836"
  by (goc_eval goc_nc_1836)

lemma goc_nc_1837: "goc_sub None 1837"
  by (goc_eval goc_nc_1837)

lemma goc_nc_1838: "goc_sub None 1838"
  by (goc_eval goc_nc_1838)

lemma goc_nc_1839: "goc_sub None 1839"
  by (goc_eval goc_nc_1839)

lemma gupt_nc_114: "[1824..<1840] = [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]"
  by (simp add: upt_rec)

lemma gsec_nc_114: "\<forall>j\<in>{16 * 114..<16 * 114 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 114..<16 * 114 + 16}"
  then have "j \<in> set [1824..<1840]" unfolding set_upt by simp
  then have "j \<in> set [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]" unfolding gupt_nc_114 .
  then show "goc_sub None j" using goc_nc_1824 goc_nc_1825 goc_nc_1826 goc_nc_1827 goc_nc_1828 goc_nc_1829 goc_nc_1830 goc_nc_1831 goc_nc_1832 goc_nc_1833 goc_nc_1834 goc_nc_1835 goc_nc_1836 goc_nc_1837 goc_nc_1838 goc_nc_1839
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
