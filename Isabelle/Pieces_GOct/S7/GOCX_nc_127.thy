theory GOCX_nc_127
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2032: "goc_sub None 2032"
  by (goc_eval goc_nc_2032)

lemma goc_nc_2033: "goc_sub None 2033"
  by (goc_eval goc_nc_2033)

lemma goc_nc_2034: "goc_sub None 2034"
  by (goc_eval goc_nc_2034)

lemma goc_nc_2035: "goc_sub None 2035"
  by (goc_eval goc_nc_2035)

lemma goc_nc_2036: "goc_sub None 2036"
  by (goc_eval goc_nc_2036)

lemma goc_nc_2037: "goc_sub None 2037"
  by (goc_eval goc_nc_2037)

lemma goc_nc_2038: "goc_sub None 2038"
  by (goc_eval goc_nc_2038)

lemma goc_nc_2039: "goc_sub None 2039"
  by (goc_eval goc_nc_2039)

lemma goc_nc_2040: "goc_sub None 2040"
  by (goc_eval goc_nc_2040)

lemma goc_nc_2041: "goc_sub None 2041"
  by (goc_eval goc_nc_2041)

lemma goc_nc_2042: "goc_sub None 2042"
  by (goc_eval goc_nc_2042)

lemma goc_nc_2043: "goc_sub None 2043"
  by (goc_eval goc_nc_2043)

lemma goc_nc_2044: "goc_sub None 2044"
  by (goc_eval goc_nc_2044)

lemma goc_nc_2045: "goc_sub None 2045"
  by (goc_eval goc_nc_2045)

lemma goc_nc_2046: "goc_sub None 2046"
  by (goc_eval goc_nc_2046)

lemma goc_nc_2047: "goc_sub None 2047"
  by (goc_eval goc_nc_2047)

lemma gupt_nc_127: "[2032..<2048] = [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]"
  by (simp add: upt_rec)

lemma gsec_nc_127: "\<forall>j\<in>{16 * 127..<16 * 127 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 127..<16 * 127 + 16}"
  then have "j \<in> set [2032..<2048]" unfolding set_upt by simp
  then have "j \<in> set [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]" unfolding gupt_nc_127 .
  then show "goc_sub None j" using goc_nc_2032 goc_nc_2033 goc_nc_2034 goc_nc_2035 goc_nc_2036 goc_nc_2037 goc_nc_2038 goc_nc_2039 goc_nc_2040 goc_nc_2041 goc_nc_2042 goc_nc_2043 goc_nc_2044 goc_nc_2045 goc_nc_2046 goc_nc_2047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
