theory GOCX_nc_112
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1792: "goc_sub None 1792"
  by (goc_eval goc_nc_1792)

lemma goc_nc_1793: "goc_sub None 1793"
  by (goc_eval goc_nc_1793)

lemma goc_nc_1794: "goc_sub None 1794"
  by (goc_eval goc_nc_1794)

lemma goc_nc_1795: "goc_sub None 1795"
  by (goc_eval goc_nc_1795)

lemma goc_nc_1796: "goc_sub None 1796"
  by (goc_eval goc_nc_1796)

lemma goc_nc_1797: "goc_sub None 1797"
  by (goc_eval goc_nc_1797)

lemma goc_nc_1798: "goc_sub None 1798"
  by (goc_eval goc_nc_1798)

lemma goc_nc_1799: "goc_sub None 1799"
  by (goc_eval goc_nc_1799)

lemma goc_nc_1800: "goc_sub None 1800"
  by (goc_eval goc_nc_1800)

lemma goc_nc_1801: "goc_sub None 1801"
  by (goc_eval goc_nc_1801)

lemma goc_nc_1802: "goc_sub None 1802"
  by (goc_eval goc_nc_1802)

lemma goc_nc_1803: "goc_sub None 1803"
  by (goc_eval goc_nc_1803)

lemma goc_nc_1804: "goc_sub None 1804"
  by (goc_eval goc_nc_1804)

lemma goc_nc_1805: "goc_sub None 1805"
  by (goc_eval goc_nc_1805)

lemma goc_nc_1806: "goc_sub None 1806"
  by (goc_eval goc_nc_1806)

lemma goc_nc_1807: "goc_sub None 1807"
  by (goc_eval goc_nc_1807)

lemma gupt_nc_112: "[1792..<1808] = [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]"
  by (simp add: upt_rec)

lemma gsec_nc_112: "\<forall>j\<in>{16 * 112..<16 * 112 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 112..<16 * 112 + 16}"
  then have "j \<in> set [1792..<1808]" unfolding set_upt by simp
  then have "j \<in> set [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]" unfolding gupt_nc_112 .
  then show "goc_sub None j" using goc_nc_1792 goc_nc_1793 goc_nc_1794 goc_nc_1795 goc_nc_1796 goc_nc_1797 goc_nc_1798 goc_nc_1799 goc_nc_1800 goc_nc_1801 goc_nc_1802 goc_nc_1803 goc_nc_1804 goc_nc_1805 goc_nc_1806 goc_nc_1807
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
