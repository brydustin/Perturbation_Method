theory OCX_c30_112
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1792: "oc_sub oc_b30 1792"
  by (oc_eval oc_c30_1792)

lemma oc_c30_1793: "oc_sub oc_b30 1793"
  by (oc_eval oc_c30_1793)

lemma oc_c30_1794: "oc_sub oc_b30 1794"
  by (oc_eval oc_c30_1794)

lemma oc_c30_1795: "oc_sub oc_b30 1795"
  by (oc_eval oc_c30_1795)

lemma oc_c30_1796: "oc_sub oc_b30 1796"
  by (oc_eval oc_c30_1796)

lemma oc_c30_1797: "oc_sub oc_b30 1797"
  by (oc_eval oc_c30_1797)

lemma oc_c30_1798: "oc_sub oc_b30 1798"
  by (oc_eval oc_c30_1798)

lemma oc_c30_1799: "oc_sub oc_b30 1799"
  by (oc_eval oc_c30_1799)

lemma oc_c30_1800: "oc_sub oc_b30 1800"
  by (oc_eval oc_c30_1800)

lemma oc_c30_1801: "oc_sub oc_b30 1801"
  by (oc_eval oc_c30_1801)

lemma oc_c30_1802: "oc_sub oc_b30 1802"
  by (oc_eval oc_c30_1802)

lemma oc_c30_1803: "oc_sub oc_b30 1803"
  by (oc_eval oc_c30_1803)

lemma oc_c30_1804: "oc_sub oc_b30 1804"
  by (oc_eval oc_c30_1804)

lemma oc_c30_1805: "oc_sub oc_b30 1805"
  by (oc_eval oc_c30_1805)

lemma oc_c30_1806: "oc_sub oc_b30 1806"
  by (oc_eval oc_c30_1806)

lemma oc_c30_1807: "oc_sub oc_b30 1807"
  by (oc_eval oc_c30_1807)

lemma upt_c30_112: "[1792..<1808] = [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]"
  by (simp add: upt_rec)

lemma sec_c30_112: "\<forall>j\<in>{16 * 112..<16 * 112 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 112..<16 * 112 + 16}"
  then have "j \<in> set [1792..<1808]" unfolding set_upt by simp
  then have "j \<in> set [1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807]" unfolding upt_c30_112 .
  then show "oc_sub oc_b30 j" using oc_c30_1792 oc_c30_1793 oc_c30_1794 oc_c30_1795 oc_c30_1796 oc_c30_1797 oc_c30_1798 oc_c30_1799 oc_c30_1800 oc_c30_1801 oc_c30_1802 oc_c30_1803 oc_c30_1804 oc_c30_1805 oc_c30_1806 oc_c30_1807
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
