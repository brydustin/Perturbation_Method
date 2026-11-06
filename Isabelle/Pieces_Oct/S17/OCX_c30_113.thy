theory OCX_c30_113
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1808: "oc_sub oc_b30 1808"
  by (oc_eval oc_c30_1808)

lemma oc_c30_1809: "oc_sub oc_b30 1809"
  by (oc_eval oc_c30_1809)

lemma oc_c30_1810: "oc_sub oc_b30 1810"
  by (oc_eval oc_c30_1810)

lemma oc_c30_1811: "oc_sub oc_b30 1811"
  by (oc_eval oc_c30_1811)

lemma oc_c30_1812: "oc_sub oc_b30 1812"
  by (oc_eval oc_c30_1812)

lemma oc_c30_1813: "oc_sub oc_b30 1813"
  by (oc_eval oc_c30_1813)

lemma oc_c30_1814: "oc_sub oc_b30 1814"
  by (oc_eval oc_c30_1814)

lemma oc_c30_1815: "oc_sub oc_b30 1815"
  by (oc_eval oc_c30_1815)

lemma oc_c30_1816: "oc_sub oc_b30 1816"
  by (oc_eval oc_c30_1816)

lemma oc_c30_1817: "oc_sub oc_b30 1817"
  by (oc_eval oc_c30_1817)

lemma oc_c30_1818: "oc_sub oc_b30 1818"
  by (oc_eval oc_c30_1818)

lemma oc_c30_1819: "oc_sub oc_b30 1819"
  by (oc_eval oc_c30_1819)

lemma oc_c30_1820: "oc_sub oc_b30 1820"
  by (oc_eval oc_c30_1820)

lemma oc_c30_1821: "oc_sub oc_b30 1821"
  by (oc_eval oc_c30_1821)

lemma oc_c30_1822: "oc_sub oc_b30 1822"
  by (oc_eval oc_c30_1822)

lemma oc_c30_1823: "oc_sub oc_b30 1823"
  by (oc_eval oc_c30_1823)

lemma upt_c30_113: "[1808..<1824] = [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]"
  by (simp add: upt_rec)

lemma sec_c30_113: "\<forall>j\<in>{16 * 113..<16 * 113 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 113..<16 * 113 + 16}"
  then have "j \<in> set [1808..<1824]" unfolding set_upt by simp
  then have "j \<in> set [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]" unfolding upt_c30_113 .
  then show "oc_sub oc_b30 j" using oc_c30_1808 oc_c30_1809 oc_c30_1810 oc_c30_1811 oc_c30_1812 oc_c30_1813 oc_c30_1814 oc_c30_1815 oc_c30_1816 oc_c30_1817 oc_c30_1818 oc_c30_1819 oc_c30_1820 oc_c30_1821 oc_c30_1822 oc_c30_1823
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
