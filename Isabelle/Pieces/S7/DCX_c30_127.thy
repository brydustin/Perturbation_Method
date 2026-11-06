theory DCX_c30_127
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2032: "dc_sub dc_b30 2032"
  by (dc_eval dc_c30_2032)

lemma dc_c30_2033: "dc_sub dc_b30 2033"
  by (dc_eval dc_c30_2033)

lemma dc_c30_2034: "dc_sub dc_b30 2034"
  by (dc_eval dc_c30_2034)

lemma dc_c30_2035: "dc_sub dc_b30 2035"
  by (dc_eval dc_c30_2035)

lemma dc_c30_2036: "dc_sub dc_b30 2036"
  by (dc_eval dc_c30_2036)

lemma dc_c30_2037: "dc_sub dc_b30 2037"
  by (dc_eval dc_c30_2037)

lemma dc_c30_2038: "dc_sub dc_b30 2038"
  by (dc_eval dc_c30_2038)

lemma dc_c30_2039: "dc_sub dc_b30 2039"
  by (dc_eval dc_c30_2039)

lemma dc_c30_2040: "dc_sub dc_b30 2040"
  by (dc_eval dc_c30_2040)

lemma dc_c30_2041: "dc_sub dc_b30 2041"
  by (dc_eval dc_c30_2041)

lemma dc_c30_2042: "dc_sub dc_b30 2042"
  by (dc_eval dc_c30_2042)

lemma dc_c30_2043: "dc_sub dc_b30 2043"
  by (dc_eval dc_c30_2043)

lemma dc_c30_2044: "dc_sub dc_b30 2044"
  by (dc_eval dc_c30_2044)

lemma dc_c30_2045: "dc_sub dc_b30 2045"
  by (dc_eval dc_c30_2045)

lemma dc_c30_2046: "dc_sub dc_b30 2046"
  by (dc_eval dc_c30_2046)

lemma dc_c30_2047: "dc_sub dc_b30 2047"
  by (dc_eval dc_c30_2047)

lemma upt_c30_127: "[2032..<2048] = [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]"
  by (simp add: upt_rec)

lemma sec_c30_127: "\<forall>j\<in>{16 * 127..<16 * 127 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 127..<16 * 127 + 16}"
  then have "j \<in> set [2032..<2048]" unfolding set_upt by simp
  then have "j \<in> set [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]" unfolding upt_c30_127 .
  then show "dc_sub dc_b30 j" using dc_c30_2032 dc_c30_2033 dc_c30_2034 dc_c30_2035 dc_c30_2036 dc_c30_2037 dc_c30_2038 dc_c30_2039 dc_c30_2040 dc_c30_2041 dc_c30_2042 dc_c30_2043 dc_c30_2044 dc_c30_2045 dc_c30_2046 dc_c30_2047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
