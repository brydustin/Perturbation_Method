theory DCX_c30_114
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1824: "dc_sub dc_b30 1824"
  by (dc_eval dc_c30_1824)

lemma dc_c30_1825: "dc_sub dc_b30 1825"
  by (dc_eval dc_c30_1825)

lemma dc_c30_1826: "dc_sub dc_b30 1826"
  by (dc_eval dc_c30_1826)

lemma dc_c30_1827: "dc_sub dc_b30 1827"
  by (dc_eval dc_c30_1827)

lemma dc_c30_1828: "dc_sub dc_b30 1828"
  by (dc_eval dc_c30_1828)

lemma dc_c30_1829: "dc_sub dc_b30 1829"
  by (dc_eval dc_c30_1829)

lemma dc_c30_1830: "dc_sub dc_b30 1830"
  by (dc_eval dc_c30_1830)

lemma dc_c30_1831: "dc_sub dc_b30 1831"
  by (dc_eval dc_c30_1831)

lemma dc_c30_1832: "dc_sub dc_b30 1832"
  by (dc_eval dc_c30_1832)

lemma dc_c30_1833: "dc_sub dc_b30 1833"
  by (dc_eval dc_c30_1833)

lemma dc_c30_1834: "dc_sub dc_b30 1834"
  by (dc_eval dc_c30_1834)

lemma dc_c30_1835: "dc_sub dc_b30 1835"
  by (dc_eval dc_c30_1835)

lemma dc_c30_1836: "dc_sub dc_b30 1836"
  by (dc_eval dc_c30_1836)

lemma dc_c30_1837: "dc_sub dc_b30 1837"
  by (dc_eval dc_c30_1837)

lemma dc_c30_1838: "dc_sub dc_b30 1838"
  by (dc_eval dc_c30_1838)

lemma dc_c30_1839: "dc_sub dc_b30 1839"
  by (dc_eval dc_c30_1839)

lemma upt_c30_114: "[1824..<1840] = [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]"
  by (simp add: upt_rec)

lemma sec_c30_114: "\<forall>j\<in>{16 * 114..<16 * 114 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 114..<16 * 114 + 16}"
  then have "j \<in> set [1824..<1840]" unfolding set_upt by simp
  then have "j \<in> set [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]" unfolding upt_c30_114 .
  then show "dc_sub dc_b30 j" using dc_c30_1824 dc_c30_1825 dc_c30_1826 dc_c30_1827 dc_c30_1828 dc_c30_1829 dc_c30_1830 dc_c30_1831 dc_c30_1832 dc_c30_1833 dc_c30_1834 dc_c30_1835 dc_c30_1836 dc_c30_1837 dc_c30_1838 dc_c30_1839
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
