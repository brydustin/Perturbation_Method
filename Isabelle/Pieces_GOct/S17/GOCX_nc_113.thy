theory GOCX_nc_113
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1808: "goc_sub None 1808"
  by (goc_eval goc_nc_1808)

lemma goc_nc_1809: "goc_sub None 1809"
  by (goc_eval goc_nc_1809)

lemma goc_nc_1810: "goc_sub None 1810"
  by (goc_eval goc_nc_1810)

lemma goc_nc_1811: "goc_sub None 1811"
  by (goc_eval goc_nc_1811)

lemma goc_nc_1812: "goc_sub None 1812"
  by (goc_eval goc_nc_1812)

lemma goc_nc_1813: "goc_sub None 1813"
  by (goc_eval goc_nc_1813)

lemma goc_nc_1814: "goc_sub None 1814"
  by (goc_eval goc_nc_1814)

lemma goc_nc_1815: "goc_sub None 1815"
  by (goc_eval goc_nc_1815)

lemma goc_nc_1816: "goc_sub None 1816"
  by (goc_eval goc_nc_1816)

lemma goc_nc_1817: "goc_sub None 1817"
  by (goc_eval goc_nc_1817)

lemma goc_nc_1818: "goc_sub None 1818"
  by (goc_eval goc_nc_1818)

lemma goc_nc_1819: "goc_sub None 1819"
  by (goc_eval goc_nc_1819)

lemma goc_nc_1820: "goc_sub None 1820"
  by (goc_eval goc_nc_1820)

lemma goc_nc_1821: "goc_sub None 1821"
  by (goc_eval goc_nc_1821)

lemma goc_nc_1822: "goc_sub None 1822"
  by (goc_eval goc_nc_1822)

lemma goc_nc_1823: "goc_sub None 1823"
  by (goc_eval goc_nc_1823)

lemma gupt_nc_113: "[1808..<1824] = [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]"
  by (simp add: upt_rec)

lemma gsec_nc_113: "\<forall>j\<in>{16 * 113..<16 * 113 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 113..<16 * 113 + 16}"
  then have "j \<in> set [1808..<1824]" unfolding set_upt by simp
  then have "j \<in> set [1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823]" unfolding gupt_nc_113 .
  then show "goc_sub None j" using goc_nc_1808 goc_nc_1809 goc_nc_1810 goc_nc_1811 goc_nc_1812 goc_nc_1813 goc_nc_1814 goc_nc_1815 goc_nc_1816 goc_nc_1817 goc_nc_1818 goc_nc_1819 goc_nc_1820 goc_nc_1821 goc_nc_1822 goc_nc_1823
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
