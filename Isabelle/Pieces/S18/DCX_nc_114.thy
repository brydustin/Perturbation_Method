theory DCX_nc_114
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1824: "dc_sub None 1824"
  by (dc_eval dc_nc_1824)

lemma dc_nc_1825: "dc_sub None 1825"
  by (dc_eval dc_nc_1825)

lemma dc_nc_1826: "dc_sub None 1826"
  by (dc_eval dc_nc_1826)

lemma dc_nc_1827: "dc_sub None 1827"
  by (dc_eval dc_nc_1827)

lemma dc_nc_1828: "dc_sub None 1828"
  by (dc_eval dc_nc_1828)

lemma dc_nc_1829: "dc_sub None 1829"
  by (dc_eval dc_nc_1829)

lemma dc_nc_1830: "dc_sub None 1830"
  by (dc_eval dc_nc_1830)

lemma dc_nc_1831: "dc_sub None 1831"
  by (dc_eval dc_nc_1831)

lemma dc_nc_1832: "dc_sub None 1832"
  by (dc_eval dc_nc_1832)

lemma dc_nc_1833: "dc_sub None 1833"
  by (dc_eval dc_nc_1833)

lemma dc_nc_1834: "dc_sub None 1834"
  by (dc_eval dc_nc_1834)

lemma dc_nc_1835: "dc_sub None 1835"
  by (dc_eval dc_nc_1835)

lemma dc_nc_1836: "dc_sub None 1836"
  by (dc_eval dc_nc_1836)

lemma dc_nc_1837: "dc_sub None 1837"
  by (dc_eval dc_nc_1837)

lemma dc_nc_1838: "dc_sub None 1838"
  by (dc_eval dc_nc_1838)

lemma dc_nc_1839: "dc_sub None 1839"
  by (dc_eval dc_nc_1839)

lemma upt_nc_114: "[1824..<1840] = [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]"
  by (simp add: upt_rec)

lemma sec_nc_114: "\<forall>j\<in>{16 * 114..<16 * 114 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 114..<16 * 114 + 16}"
  then have "j \<in> set [1824..<1840]" unfolding set_upt by simp
  then have "j \<in> set [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]" unfolding upt_nc_114 .
  then show "dc_sub None j" using dc_nc_1824 dc_nc_1825 dc_nc_1826 dc_nc_1827 dc_nc_1828 dc_nc_1829 dc_nc_1830 dc_nc_1831 dc_nc_1832 dc_nc_1833 dc_nc_1834 dc_nc_1835 dc_nc_1836 dc_nc_1837 dc_nc_1838 dc_nc_1839
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
