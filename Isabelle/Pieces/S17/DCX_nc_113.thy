theory DCX_nc_113
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1808: "dc_sub None 1808"
  by (dc_eval dc_nc_1808)

lemma dc_nc_1809: "dc_sub None 1809"
  by (dc_eval dc_nc_1809)

lemma dc_nc_1810: "dc_sub None 1810"
  by (dc_eval dc_nc_1810)

lemma dc_nc_1811: "dc_sub None 1811"
  by (dc_eval dc_nc_1811)

lemma dc_nc_1812: "dc_sub None 1812"
  by (dc_eval dc_nc_1812)

lemma dc_nc_1813: "dc_sub None 1813"
  by (dc_eval dc_nc_1813)

lemma dc_nc_1814: "dc_sub None 1814"
  by (dc_eval dc_nc_1814)

lemma dc_nc_1815: "dc_sub None 1815"
  by (dc_eval dc_nc_1815)

lemma dc_nc_1816: "dc_sub None 1816"
  by (dc_eval dc_nc_1816)

lemma dc_nc_1817: "dc_sub None 1817"
  by (dc_eval dc_nc_1817)

lemma dc_nc_1818: "dc_sub None 1818"
  by (dc_eval dc_nc_1818)

lemma dc_nc_1819: "dc_sub None 1819"
  by (dc_eval dc_nc_1819)

lemma dc_nc_1820: "dc_sub None 1820"
  by (dc_eval dc_nc_1820)

lemma dc_nc_1821: "dc_sub None 1821"
  by (dc_eval dc_nc_1821)

lemma dc_nc_1822: "dc_sub None 1822"
  by (dc_eval dc_nc_1822)

lemma dc_nc_1823: "dc_sub None 1823"
  by (dc_eval dc_nc_1823)

lemma upt_nc_113: "[1808..<1824] = [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]"
  by (simp add: upt_rec)

lemma sec_nc_113: "\<forall>j\<in>{16 * 113..<16 * 113 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 113..<16 * 113 + 16}"
  then have "j \<in> set [1808..<1824]" unfolding set_upt by simp
  then have "j \<in> set [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]" unfolding upt_nc_113 .
  then show "dc_sub None j" using dc_nc_1808 dc_nc_1809 dc_nc_1810 dc_nc_1811 dc_nc_1812 dc_nc_1813 dc_nc_1814 dc_nc_1815 dc_nc_1816 dc_nc_1817 dc_nc_1818 dc_nc_1819 dc_nc_1820 dc_nc_1821 dc_nc_1822 dc_nc_1823
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
