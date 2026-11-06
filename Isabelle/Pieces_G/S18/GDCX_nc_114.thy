theory GDCX_nc_114
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1824: "gdc_sub None 1824"
  by (gdc_eval gdc_nc_1824)

lemma gdc_nc_1825: "gdc_sub None 1825"
  by (gdc_eval gdc_nc_1825)

lemma gdc_nc_1826: "gdc_sub None 1826"
  by (gdc_eval gdc_nc_1826)

lemma gdc_nc_1827: "gdc_sub None 1827"
  by (gdc_eval gdc_nc_1827)

lemma gdc_nc_1828: "gdc_sub None 1828"
  by (gdc_eval gdc_nc_1828)

lemma gdc_nc_1829: "gdc_sub None 1829"
  by (gdc_eval gdc_nc_1829)

lemma gdc_nc_1830: "gdc_sub None 1830"
  by (gdc_eval gdc_nc_1830)

lemma gdc_nc_1831: "gdc_sub None 1831"
  by (gdc_eval gdc_nc_1831)

lemma gdc_nc_1832: "gdc_sub None 1832"
  by (gdc_eval gdc_nc_1832)

lemma gdc_nc_1833: "gdc_sub None 1833"
  by (gdc_eval gdc_nc_1833)

lemma gdc_nc_1834: "gdc_sub None 1834"
  by (gdc_eval gdc_nc_1834)

lemma gdc_nc_1835: "gdc_sub None 1835"
  by (gdc_eval gdc_nc_1835)

lemma gdc_nc_1836: "gdc_sub None 1836"
  by (gdc_eval gdc_nc_1836)

lemma gdc_nc_1837: "gdc_sub None 1837"
  by (gdc_eval gdc_nc_1837)

lemma gdc_nc_1838: "gdc_sub None 1838"
  by (gdc_eval gdc_nc_1838)

lemma gdc_nc_1839: "gdc_sub None 1839"
  by (gdc_eval gdc_nc_1839)

lemma gupt_nc_114: "[1824..<1840] = [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]"
  by (simp add: upt_rec)

lemma gsec_nc_114: "\<forall>j\<in>{16 * 114..<16 * 114 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 114..<16 * 114 + 16}"
  then have "j \<in> set [1824..<1840]" unfolding set_upt by simp
  then have "j \<in> set [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]" unfolding gupt_nc_114 .
  then show "gdc_sub None j" using gdc_nc_1824 gdc_nc_1825 gdc_nc_1826 gdc_nc_1827 gdc_nc_1828 gdc_nc_1829 gdc_nc_1830 gdc_nc_1831 gdc_nc_1832 gdc_nc_1833 gdc_nc_1834 gdc_nc_1835 gdc_nc_1836 gdc_nc_1837 gdc_nc_1838 gdc_nc_1839
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
