theory OCX_nc_113
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1808: "oc_sub None 1808"
  by (oc_eval oc_nc_1808)

lemma oc_nc_1809: "oc_sub None 1809"
  by (oc_eval oc_nc_1809)

lemma oc_nc_1810: "oc_sub None 1810"
  by (oc_eval oc_nc_1810)

lemma oc_nc_1811: "oc_sub None 1811"
  by (oc_eval oc_nc_1811)

lemma oc_nc_1812: "oc_sub None 1812"
  by (oc_eval oc_nc_1812)

lemma oc_nc_1813: "oc_sub None 1813"
  by (oc_eval oc_nc_1813)

lemma oc_nc_1814: "oc_sub None 1814"
  by (oc_eval oc_nc_1814)

lemma oc_nc_1815: "oc_sub None 1815"
  by (oc_eval oc_nc_1815)

lemma oc_nc_1816: "oc_sub None 1816"
  by (oc_eval oc_nc_1816)

lemma oc_nc_1817: "oc_sub None 1817"
  by (oc_eval oc_nc_1817)

lemma oc_nc_1818: "oc_sub None 1818"
  by (oc_eval oc_nc_1818)

lemma oc_nc_1819: "oc_sub None 1819"
  by (oc_eval oc_nc_1819)

lemma oc_nc_1820: "oc_sub None 1820"
  by (oc_eval oc_nc_1820)

lemma oc_nc_1821: "oc_sub None 1821"
  by (oc_eval oc_nc_1821)

lemma oc_nc_1822: "oc_sub None 1822"
  by (oc_eval oc_nc_1822)

lemma oc_nc_1823: "oc_sub None 1823"
  by (oc_eval oc_nc_1823)

lemma upt_nc_113: "[1808..<1824] = [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]"
  by (simp add: upt_rec)

lemma sec_nc_113: "\<forall>j\<in>{16 * 113..<16 * 113 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 113..<16 * 113 + 16}"
  then have "j \<in> set [1808..<1824]" unfolding set_upt by simp
  then have "j \<in> set [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]" unfolding upt_nc_113 .
  then show "oc_sub None j" using oc_nc_1808 oc_nc_1809 oc_nc_1810 oc_nc_1811 oc_nc_1812 oc_nc_1813 oc_nc_1814 oc_nc_1815 oc_nc_1816 oc_nc_1817 oc_nc_1818 oc_nc_1819 oc_nc_1820 oc_nc_1821 oc_nc_1822 oc_nc_1823
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
