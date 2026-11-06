theory OCX_nc_127
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2032: "oc_sub None 2032"
  by (oc_eval oc_nc_2032)

lemma oc_nc_2033: "oc_sub None 2033"
  by (oc_eval oc_nc_2033)

lemma oc_nc_2034: "oc_sub None 2034"
  by (oc_eval oc_nc_2034)

lemma oc_nc_2035: "oc_sub None 2035"
  by (oc_eval oc_nc_2035)

lemma oc_nc_2036: "oc_sub None 2036"
  by (oc_eval oc_nc_2036)

lemma oc_nc_2037: "oc_sub None 2037"
  by (oc_eval oc_nc_2037)

lemma oc_nc_2038: "oc_sub None 2038"
  by (oc_eval oc_nc_2038)

lemma oc_nc_2039: "oc_sub None 2039"
  by (oc_eval oc_nc_2039)

lemma oc_nc_2040: "oc_sub None 2040"
  by (oc_eval oc_nc_2040)

lemma oc_nc_2041: "oc_sub None 2041"
  by (oc_eval oc_nc_2041)

lemma oc_nc_2042: "oc_sub None 2042"
  by (oc_eval oc_nc_2042)

lemma oc_nc_2043: "oc_sub None 2043"
  by (oc_eval oc_nc_2043)

lemma oc_nc_2044: "oc_sub None 2044"
  by (oc_eval oc_nc_2044)

lemma oc_nc_2045: "oc_sub None 2045"
  by (oc_eval oc_nc_2045)

lemma oc_nc_2046: "oc_sub None 2046"
  by (oc_eval oc_nc_2046)

lemma oc_nc_2047: "oc_sub None 2047"
  by (oc_eval oc_nc_2047)

lemma upt_nc_127: "[2032..<2048] = [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]"
  by (simp add: upt_rec)

lemma sec_nc_127: "\<forall>j\<in>{16 * 127..<16 * 127 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 127..<16 * 127 + 16}"
  then have "j \<in> set [2032..<2048]" unfolding set_upt by simp
  then have "j \<in> set [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]" unfolding upt_nc_127 .
  then show "oc_sub None j" using oc_nc_2032 oc_nc_2033 oc_nc_2034 oc_nc_2035 oc_nc_2036 oc_nc_2037 oc_nc_2038 oc_nc_2039 oc_nc_2040 oc_nc_2041 oc_nc_2042 oc_nc_2043 oc_nc_2044 oc_nc_2045 oc_nc_2046 oc_nc_2047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
