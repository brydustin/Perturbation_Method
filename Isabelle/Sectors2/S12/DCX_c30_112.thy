theory DCX_c30_112
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1792: "dc_sub dc_b30 1792"
  by (dc_eval dc_c30_1792)

lemma dc_c30_1793: "dc_sub dc_b30 1793"
  by (dc_eval dc_c30_1793)

lemma dc_c30_1794: "dc_sub dc_b30 1794"
  by (dc_eval dc_c30_1794)

lemma dc_c30_1795: "dc_sub dc_b30 1795"
  by (dc_eval dc_c30_1795)

lemma dc_c30_1796: "dc_sub dc_b30 1796"
  by (dc_eval dc_c30_1796)

lemma dc_c30_1797: "dc_sub dc_b30 1797"
  by (dc_eval dc_c30_1797)

lemma dc_c30_1798: "dc_sub dc_b30 1798"
  by (dc_eval dc_c30_1798)

lemma dc_c30_1799: "dc_sub dc_b30 1799"
  by (dc_eval dc_c30_1799)

lemma dc_c30_1800: "dc_sub dc_b30 1800"
  by (dc_eval dc_c30_1800)

lemma dc_c30_1801: "dc_sub dc_b30 1801"
  by (dc_eval dc_c30_1801)

lemma dc_c30_1802: "dc_sub dc_b30 1802"
  by (dc_eval dc_c30_1802)

lemma dc_c30_1803: "dc_sub dc_b30 1803"
  by (dc_eval dc_c30_1803)

lemma dc_c30_1804: "dc_sub dc_b30 1804"
  by (dc_eval dc_c30_1804)

lemma dc_c30_1805: "dc_sub dc_b30 1805"
  by (dc_eval dc_c30_1805)

lemma dc_c30_1806: "dc_sub dc_b30 1806"
  by (dc_eval dc_c30_1806)

lemma dc_c30_1807: "dc_sub dc_b30 1807"
  by (dc_eval dc_c30_1807)

lemma upt_c30_112: "[1792..<1808] = [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]"
  by (simp add: upt_rec)

lemma sec_c30_112: "\<forall>j\<in>{16 * 112..<16 * 112 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 112..<16 * 112 + 16}"
  then have "j \<in> set [1792..<1808]" unfolding set_upt by simp
  then have "j \<in> set [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]" unfolding upt_c30_112 .
  then show "dc_sub dc_b30 j" using dc_c30_1792 dc_c30_1793 dc_c30_1794 dc_c30_1795 dc_c30_1796 dc_c30_1797 dc_c30_1798 dc_c30_1799 dc_c30_1800 dc_c30_1801 dc_c30_1802 dc_c30_1803 dc_c30_1804 dc_c30_1805 dc_c30_1806 dc_c30_1807
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
