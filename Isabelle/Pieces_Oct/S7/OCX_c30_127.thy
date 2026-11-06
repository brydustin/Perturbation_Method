theory OCX_c30_127
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2032: "oc_sub oc_b30 2032"
  by (oc_eval oc_c30_2032)

lemma oc_c30_2033: "oc_sub oc_b30 2033"
  by (oc_eval oc_c30_2033)

lemma oc_c30_2034: "oc_sub oc_b30 2034"
  by (oc_eval oc_c30_2034)

lemma oc_c30_2035: "oc_sub oc_b30 2035"
  by (oc_eval oc_c30_2035)

lemma oc_c30_2036: "oc_sub oc_b30 2036"
  by (oc_eval oc_c30_2036)

lemma oc_c30_2037: "oc_sub oc_b30 2037"
  by (oc_eval oc_c30_2037)

lemma oc_c30_2038: "oc_sub oc_b30 2038"
  by (oc_eval oc_c30_2038)

lemma oc_c30_2039: "oc_sub oc_b30 2039"
  by (oc_eval oc_c30_2039)

lemma oc_c30_2040: "oc_sub oc_b30 2040"
  by (oc_eval oc_c30_2040)

lemma oc_c30_2041: "oc_sub oc_b30 2041"
  by (oc_eval oc_c30_2041)

lemma oc_c30_2042: "oc_sub oc_b30 2042"
  by (oc_eval oc_c30_2042)

lemma oc_c30_2043: "oc_sub oc_b30 2043"
  by (oc_eval oc_c30_2043)

lemma oc_c30_2044: "oc_sub oc_b30 2044"
  by (oc_eval oc_c30_2044)

lemma oc_c30_2045: "oc_sub oc_b30 2045"
  by (oc_eval oc_c30_2045)

lemma oc_c30_2046: "oc_sub oc_b30 2046"
  by (oc_eval oc_c30_2046)

lemma oc_c30_2047: "oc_sub oc_b30 2047"
  by (oc_eval oc_c30_2047)

lemma upt_c30_127: "[2032..<2048] = [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]"
  by (simp add: upt_rec)

lemma sec_c30_127: "\<forall>j\<in>{16 * 127..<16 * 127 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 127..<16 * 127 + 16}"
  then have "j \<in> set [2032..<2048]" unfolding set_upt by simp
  then have "j \<in> set [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]" unfolding upt_c30_127 .
  then show "oc_sub oc_b30 j" using oc_c30_2032 oc_c30_2033 oc_c30_2034 oc_c30_2035 oc_c30_2036 oc_c30_2037 oc_c30_2038 oc_c30_2039 oc_c30_2040 oc_c30_2041 oc_c30_2042 oc_c30_2043 oc_c30_2044 oc_c30_2045 oc_c30_2046 oc_c30_2047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
