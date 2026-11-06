theory GDCX_nc_112
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1792: "gdc_sub None 1792"
  by (gdc_eval gdc_nc_1792)

lemma gdc_nc_1793: "gdc_sub None 1793"
  by (gdc_eval gdc_nc_1793)

lemma gdc_nc_1794: "gdc_sub None 1794"
  by (gdc_eval gdc_nc_1794)

lemma gdc_nc_1795: "gdc_sub None 1795"
  by (gdc_eval gdc_nc_1795)

lemma gdc_nc_1796: "gdc_sub None 1796"
  by (gdc_eval gdc_nc_1796)

lemma gdc_nc_1797: "gdc_sub None 1797"
  by (gdc_eval gdc_nc_1797)

lemma gdc_nc_1798: "gdc_sub None 1798"
  by (gdc_eval gdc_nc_1798)

lemma gdc_nc_1799: "gdc_sub None 1799"
  by (gdc_eval gdc_nc_1799)

lemma gdc_nc_1800: "gdc_sub None 1800"
  by (gdc_eval gdc_nc_1800)

lemma gdc_nc_1801: "gdc_sub None 1801"
  by (gdc_eval gdc_nc_1801)

lemma gdc_nc_1802: "gdc_sub None 1802"
  by (gdc_eval gdc_nc_1802)

lemma gdc_nc_1803: "gdc_sub None 1803"
  by (gdc_eval gdc_nc_1803)

lemma gdc_nc_1804: "gdc_sub None 1804"
  by (gdc_eval gdc_nc_1804)

lemma gdc_nc_1805: "gdc_sub None 1805"
  by (gdc_eval gdc_nc_1805)

lemma gdc_nc_1806: "gdc_sub None 1806"
  by (gdc_eval gdc_nc_1806)

lemma gdc_nc_1807: "gdc_sub None 1807"
  by (gdc_eval gdc_nc_1807)

lemma gupt_nc_112: "[1792..<1808] = [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]"
  by (simp add: upt_rec)

lemma gsec_nc_112: "\<forall>j\<in>{16 * 112..<16 * 112 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 112..<16 * 112 + 16}"
  then have "j \<in> set [1792..<1808]" unfolding set_upt by simp
  then have "j \<in> set [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]" unfolding gupt_nc_112 .
  then show "gdc_sub None j" using gdc_nc_1792 gdc_nc_1793 gdc_nc_1794 gdc_nc_1795 gdc_nc_1796 gdc_nc_1797 gdc_nc_1798 gdc_nc_1799 gdc_nc_1800 gdc_nc_1801 gdc_nc_1802 gdc_nc_1803 gdc_nc_1804 gdc_nc_1805 gdc_nc_1806 gdc_nc_1807
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
