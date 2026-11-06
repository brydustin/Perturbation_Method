theory DCX_c30_113
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1808: "dc_sub dc_b30 1808"
  by (dc_eval dc_c30_1808)

lemma dc_c30_1809: "dc_sub dc_b30 1809"
  by (dc_eval dc_c30_1809)

lemma dc_c30_1810: "dc_sub dc_b30 1810"
  by (dc_eval dc_c30_1810)

lemma dc_c30_1811: "dc_sub dc_b30 1811"
  by (dc_eval dc_c30_1811)

lemma dc_c30_1812: "dc_sub dc_b30 1812"
  by (dc_eval dc_c30_1812)

lemma dc_c30_1813: "dc_sub dc_b30 1813"
  by (dc_eval dc_c30_1813)

lemma dc_c30_1814: "dc_sub dc_b30 1814"
  by (dc_eval dc_c30_1814)

lemma dc_c30_1815: "dc_sub dc_b30 1815"
  by (dc_eval dc_c30_1815)

lemma dc_c30_1816: "dc_sub dc_b30 1816"
  by (dc_eval dc_c30_1816)

lemma dc_c30_1817: "dc_sub dc_b30 1817"
  by (dc_eval dc_c30_1817)

lemma dc_c30_1818: "dc_sub dc_b30 1818"
  by (dc_eval dc_c30_1818)

lemma dc_c30_1819: "dc_sub dc_b30 1819"
  by (dc_eval dc_c30_1819)

lemma dc_c30_1820: "dc_sub dc_b30 1820"
  by (dc_eval dc_c30_1820)

lemma dc_c30_1821: "dc_sub dc_b30 1821"
  by (dc_eval dc_c30_1821)

lemma dc_c30_1822: "dc_sub dc_b30 1822"
  by (dc_eval dc_c30_1822)

lemma dc_c30_1823: "dc_sub dc_b30 1823"
  by (dc_eval dc_c30_1823)

lemma upt_c30_113: "[1808..<1824] = [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]"
  by (simp add: upt_rec)

lemma sec_c30_113: "\<forall>j\<in>{16 * 113..<16 * 113 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 113..<16 * 113 + 16}"
  then have "j \<in> set [1808..<1824]" unfolding set_upt by simp
  then have "j \<in> set [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]" unfolding upt_c30_113 .
  then show "dc_sub dc_b30 j" using dc_c30_1808 dc_c30_1809 dc_c30_1810 dc_c30_1811 dc_c30_1812 dc_c30_1813 dc_c30_1814 dc_c30_1815 dc_c30_1816 dc_c30_1817 dc_c30_1818 dc_c30_1819 dc_c30_1820 dc_c30_1821 dc_c30_1822 dc_c30_1823
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
