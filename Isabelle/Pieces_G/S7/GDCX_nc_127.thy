theory GDCX_nc_127
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2032: "gdc_sub None 2032"
  by (gdc_eval gdc_nc_2032)

lemma gdc_nc_2033: "gdc_sub None 2033"
  by (gdc_eval gdc_nc_2033)

lemma gdc_nc_2034: "gdc_sub None 2034"
  by (gdc_eval gdc_nc_2034)

lemma gdc_nc_2035: "gdc_sub None 2035"
  by (gdc_eval gdc_nc_2035)

lemma gdc_nc_2036: "gdc_sub None 2036"
  by (gdc_eval gdc_nc_2036)

lemma gdc_nc_2037: "gdc_sub None 2037"
  by (gdc_eval gdc_nc_2037)

lemma gdc_nc_2038: "gdc_sub None 2038"
  by (gdc_eval gdc_nc_2038)

lemma gdc_nc_2039: "gdc_sub None 2039"
  by (gdc_eval gdc_nc_2039)

lemma gdc_nc_2040: "gdc_sub None 2040"
  by (gdc_eval gdc_nc_2040)

lemma gdc_nc_2041: "gdc_sub None 2041"
  by (gdc_eval gdc_nc_2041)

lemma gdc_nc_2042: "gdc_sub None 2042"
  by (gdc_eval gdc_nc_2042)

lemma gdc_nc_2043: "gdc_sub None 2043"
  by (gdc_eval gdc_nc_2043)

lemma gdc_nc_2044: "gdc_sub None 2044"
  by (gdc_eval gdc_nc_2044)

lemma gdc_nc_2045: "gdc_sub None 2045"
  by (gdc_eval gdc_nc_2045)

lemma gdc_nc_2046: "gdc_sub None 2046"
  by (gdc_eval gdc_nc_2046)

lemma gdc_nc_2047: "gdc_sub None 2047"
  by (gdc_eval gdc_nc_2047)

lemma gupt_nc_127: "[2032..<2048] = [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]"
  by (simp add: upt_rec)

lemma gsec_nc_127: "\<forall>j\<in>{16 * 127..<16 * 127 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 127..<16 * 127 + 16}"
  then have "j \<in> set [2032..<2048]" unfolding set_upt by simp
  then have "j \<in> set [2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047]" unfolding gupt_nc_127 .
  then show "gdc_sub None j" using gdc_nc_2032 gdc_nc_2033 gdc_nc_2034 gdc_nc_2035 gdc_nc_2036 gdc_nc_2037 gdc_nc_2038 gdc_nc_2039 gdc_nc_2040 gdc_nc_2041 gdc_nc_2042 gdc_nc_2043 gdc_nc_2044 gdc_nc_2045 gdc_nc_2046 gdc_nc_2047
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
