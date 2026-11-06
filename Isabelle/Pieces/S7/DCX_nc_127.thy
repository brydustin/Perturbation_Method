theory DCX_nc_127
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2032: "dc_sub None 2032"
  by (dc_eval dc_nc_2032)

lemma dc_nc_2033: "dc_sub None 2033"
  by (dc_eval dc_nc_2033)

lemma dc_nc_2034: "dc_sub None 2034"
  by (dc_eval dc_nc_2034)

lemma dc_nc_2035: "dc_sub None 2035"
  by (dc_eval dc_nc_2035)

lemma dc_nc_2036: "dc_sub None 2036"
  by (dc_eval dc_nc_2036)

lemma dc_nc_2037: "dc_sub None 2037"
  by (dc_eval dc_nc_2037)

lemma dc_nc_2038: "dc_sub None 2038"
  by (dc_eval dc_nc_2038)

lemma dc_nc_2039: "dc_sub None 2039"
  by (dc_eval dc_nc_2039)

lemma dc_nc_2040: "dc_sub None 2040"
  by (dc_eval dc_nc_2040)

lemma dc_nc_2041: "dc_sub None 2041"
  by (dc_eval dc_nc_2041)

lemma dc_nc_2042: "dc_sub None 2042"
  by (dc_eval dc_nc_2042)

lemma dc_nc_2043: "dc_sub None 2043"
  by (dc_eval dc_nc_2043)

lemma dc_nc_2044: "dc_sub None 2044"
  by (dc_eval dc_nc_2044)

lemma dc_nc_2045: "dc_sub None 2045"
  by (dc_eval dc_nc_2045)

lemma dc_nc_2046: "dc_sub None 2046"
  by (dc_eval dc_nc_2046)

lemma dc_nc_2047: "dc_sub None 2047"
  by (dc_eval dc_nc_2047)

lemma upt_nc_127: "[2032..<2048] = [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]"
  by (simp add: upt_rec)

lemma sec_nc_127: "\<forall>j\<in>{16 * 127..<16 * 127 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 127..<16 * 127 + 16}"
  then have "j \<in> set [2032..<2048]" unfolding set_upt by simp
  then have "j \<in> set [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]" unfolding upt_nc_127 .
  then show "dc_sub None j" using dc_nc_2032 dc_nc_2033 dc_nc_2034 dc_nc_2035 dc_nc_2036 dc_nc_2037 dc_nc_2038 dc_nc_2039 dc_nc_2040 dc_nc_2041 dc_nc_2042 dc_nc_2043 dc_nc_2044 dc_nc_2045 dc_nc_2046 dc_nc_2047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
