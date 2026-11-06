theory OCX_c30_114
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1824: "oc_sub oc_b30 1824"
  by (oc_eval oc_c30_1824)

lemma oc_c30_1825: "oc_sub oc_b30 1825"
  by (oc_eval oc_c30_1825)

lemma oc_c30_1826: "oc_sub oc_b30 1826"
  by (oc_eval oc_c30_1826)

lemma oc_c30_1827: "oc_sub oc_b30 1827"
  by (oc_eval oc_c30_1827)

lemma oc_c30_1828: "oc_sub oc_b30 1828"
  by (oc_eval oc_c30_1828)

lemma oc_c30_1829: "oc_sub oc_b30 1829"
  by (oc_eval oc_c30_1829)

lemma oc_c30_1830: "oc_sub oc_b30 1830"
  by (oc_eval oc_c30_1830)

lemma oc_c30_1831: "oc_sub oc_b30 1831"
  by (oc_eval oc_c30_1831)

lemma oc_c30_1832: "oc_sub oc_b30 1832"
  by (oc_eval oc_c30_1832)

lemma oc_c30_1833: "oc_sub oc_b30 1833"
  by (oc_eval oc_c30_1833)

lemma oc_c30_1834: "oc_sub oc_b30 1834"
  by (oc_eval oc_c30_1834)

lemma oc_c30_1835: "oc_sub oc_b30 1835"
  by (oc_eval oc_c30_1835)

lemma oc_c30_1836: "oc_sub oc_b30 1836"
  by (oc_eval oc_c30_1836)

lemma oc_c30_1837: "oc_sub oc_b30 1837"
  by (oc_eval oc_c30_1837)

lemma oc_c30_1838: "oc_sub oc_b30 1838"
  by (oc_eval oc_c30_1838)

lemma oc_c30_1839: "oc_sub oc_b30 1839"
  by (oc_eval oc_c30_1839)

lemma upt_c30_114: "[1824..<1840] = [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]"
  by (simp add: upt_rec)

lemma sec_c30_114: "\<forall>j\<in>{16 * 114..<16 * 114 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 114..<16 * 114 + 16}"
  then have "j \<in> set [1824..<1840]" unfolding set_upt by simp
  then have "j \<in> set [1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839]" unfolding upt_c30_114 .
  then show "oc_sub oc_b30 j" using oc_c30_1824 oc_c30_1825 oc_c30_1826 oc_c30_1827 oc_c30_1828 oc_c30_1829 oc_c30_1830 oc_c30_1831 oc_c30_1832 oc_c30_1833 oc_c30_1834 oc_c30_1835 oc_c30_1836 oc_c30_1837 oc_c30_1838 oc_c30_1839
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
