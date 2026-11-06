theory GDCX_nc_113
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1808: "gdc_sub None 1808"
  by (gdc_eval gdc_nc_1808)

lemma gdc_nc_1809: "gdc_sub None 1809"
  by (gdc_eval gdc_nc_1809)

lemma gdc_nc_1810: "gdc_sub None 1810"
  by (gdc_eval gdc_nc_1810)

lemma gdc_nc_1811: "gdc_sub None 1811"
  by (gdc_eval gdc_nc_1811)

lemma gdc_nc_1812: "gdc_sub None 1812"
  by (gdc_eval gdc_nc_1812)

lemma gdc_nc_1813: "gdc_sub None 1813"
  by (gdc_eval gdc_nc_1813)

lemma gdc_nc_1814: "gdc_sub None 1814"
  by (gdc_eval gdc_nc_1814)

lemma gdc_nc_1815: "gdc_sub None 1815"
  by (gdc_eval gdc_nc_1815)

lemma gdc_nc_1816: "gdc_sub None 1816"
  by (gdc_eval gdc_nc_1816)

lemma gdc_nc_1817: "gdc_sub None 1817"
  by (gdc_eval gdc_nc_1817)

lemma gdc_nc_1818: "gdc_sub None 1818"
  by (gdc_eval gdc_nc_1818)

lemma gdc_nc_1819: "gdc_sub None 1819"
  by (gdc_eval gdc_nc_1819)

lemma gdc_nc_1820: "gdc_sub None 1820"
  by (gdc_eval gdc_nc_1820)

lemma gdc_nc_1821: "gdc_sub None 1821"
  by (gdc_eval gdc_nc_1821)

lemma gdc_nc_1822: "gdc_sub None 1822"
  by (gdc_eval gdc_nc_1822)

lemma gdc_nc_1823: "gdc_sub None 1823"
  by (gdc_eval gdc_nc_1823)

lemma gupt_nc_113: "[1808..<1824] = [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]"
  by (simp add: upt_rec)

lemma gsec_nc_113: "\<forall>j\<in>{16 * 113..<16 * 113 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 113..<16 * 113 + 16}"
  then have "j \<in> set [1808..<1824]" unfolding set_upt by simp
  then have "j \<in> set [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]" unfolding gupt_nc_113 .
  then show "gdc_sub None j" using gdc_nc_1808 gdc_nc_1809 gdc_nc_1810 gdc_nc_1811 gdc_nc_1812 gdc_nc_1813 gdc_nc_1814 gdc_nc_1815 gdc_nc_1816 gdc_nc_1817 gdc_nc_1818 gdc_nc_1819 gdc_nc_1820 gdc_nc_1821 gdc_nc_1822 gdc_nc_1823
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
