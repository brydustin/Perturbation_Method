theory OCX_nc_112
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1792: "oc_sub None 1792"
  by (oc_eval oc_nc_1792)

lemma oc_nc_1793: "oc_sub None 1793"
  by (oc_eval oc_nc_1793)

lemma oc_nc_1794: "oc_sub None 1794"
  by (oc_eval oc_nc_1794)

lemma oc_nc_1795: "oc_sub None 1795"
  by (oc_eval oc_nc_1795)

lemma oc_nc_1796: "oc_sub None 1796"
  by (oc_eval oc_nc_1796)

lemma oc_nc_1797: "oc_sub None 1797"
  by (oc_eval oc_nc_1797)

lemma oc_nc_1798: "oc_sub None 1798"
  by (oc_eval oc_nc_1798)

lemma oc_nc_1799: "oc_sub None 1799"
  by (oc_eval oc_nc_1799)

lemma oc_nc_1800: "oc_sub None 1800"
  by (oc_eval oc_nc_1800)

lemma oc_nc_1801: "oc_sub None 1801"
  by (oc_eval oc_nc_1801)

lemma oc_nc_1802: "oc_sub None 1802"
  by (oc_eval oc_nc_1802)

lemma oc_nc_1803: "oc_sub None 1803"
  by (oc_eval oc_nc_1803)

lemma oc_nc_1804: "oc_sub None 1804"
  by (oc_eval oc_nc_1804)

lemma oc_nc_1805: "oc_sub None 1805"
  by (oc_eval oc_nc_1805)

lemma oc_nc_1806: "oc_sub None 1806"
  by (oc_eval oc_nc_1806)

lemma oc_nc_1807: "oc_sub None 1807"
  by (oc_eval oc_nc_1807)

lemma upt_nc_112: "[1792..<1808] = [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]"
  by (simp add: upt_rec)

lemma sec_nc_112: "\<forall>j\<in>{16 * 112..<16 * 112 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 112..<16 * 112 + 16}"
  then have "j \<in> set [1792..<1808]" unfolding set_upt by simp
  then have "j \<in> set [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]" unfolding upt_nc_112 .
  then show "oc_sub None j" using oc_nc_1792 oc_nc_1793 oc_nc_1794 oc_nc_1795 oc_nc_1796 oc_nc_1797 oc_nc_1798 oc_nc_1799 oc_nc_1800 oc_nc_1801 oc_nc_1802 oc_nc_1803 oc_nc_1804 oc_nc_1805 oc_nc_1806 oc_nc_1807
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
