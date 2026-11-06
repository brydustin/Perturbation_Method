theory OCX_nc_114
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1824: "oc_sub None 1824"
  by (oc_eval oc_nc_1824)

lemma oc_nc_1825: "oc_sub None 1825"
  by (oc_eval oc_nc_1825)

lemma oc_nc_1826: "oc_sub None 1826"
  by (oc_eval oc_nc_1826)

lemma oc_nc_1827: "oc_sub None 1827"
  by (oc_eval oc_nc_1827)

lemma oc_nc_1828: "oc_sub None 1828"
  by (oc_eval oc_nc_1828)

lemma oc_nc_1829: "oc_sub None 1829"
  by (oc_eval oc_nc_1829)

lemma oc_nc_1830: "oc_sub None 1830"
  by (oc_eval oc_nc_1830)

lemma oc_nc_1831: "oc_sub None 1831"
  by (oc_eval oc_nc_1831)

lemma oc_nc_1832: "oc_sub None 1832"
  by (oc_eval oc_nc_1832)

lemma oc_nc_1833: "oc_sub None 1833"
  by (oc_eval oc_nc_1833)

lemma oc_nc_1834: "oc_sub None 1834"
  by (oc_eval oc_nc_1834)

lemma oc_nc_1835: "oc_sub None 1835"
  by (oc_eval oc_nc_1835)

lemma oc_nc_1836: "oc_sub None 1836"
  by (oc_eval oc_nc_1836)

lemma oc_nc_1837: "oc_sub None 1837"
  by (oc_eval oc_nc_1837)

lemma oc_nc_1838: "oc_sub None 1838"
  by (oc_eval oc_nc_1838)

lemma oc_nc_1839: "oc_sub None 1839"
  by (oc_eval oc_nc_1839)

lemma upt_nc_114: "[1824..<1840] = [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]"
  by (simp add: upt_rec)

lemma sec_nc_114: "\<forall>j\<in>{16 * 114..<16 * 114 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 114..<16 * 114 + 16}"
  then have "j \<in> set [1824..<1840]" unfolding set_upt by simp
  then have "j \<in> set [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]" unfolding upt_nc_114 .
  then show "oc_sub None j" using oc_nc_1824 oc_nc_1825 oc_nc_1826 oc_nc_1827 oc_nc_1828 oc_nc_1829 oc_nc_1830 oc_nc_1831 oc_nc_1832 oc_nc_1833 oc_nc_1834 oc_nc_1835 oc_nc_1836 oc_nc_1837 oc_nc_1838 oc_nc_1839
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
