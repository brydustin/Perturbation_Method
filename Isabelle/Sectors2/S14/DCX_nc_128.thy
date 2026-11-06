theory DCX_nc_128
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2048: "dc_sub None 2048"
  by (dc_eval dc_nc_2048)

lemma dc_nc_2049: "dc_sub None 2049"
  by (dc_eval dc_nc_2049)

lemma dc_nc_2050: "dc_sub None 2050"
  by (dc_eval dc_nc_2050)

lemma dc_nc_2051: "dc_sub None 2051"
  by (dc_eval dc_nc_2051)

lemma dc_nc_2052: "dc_sub None 2052"
  by (dc_eval dc_nc_2052)

lemma dc_nc_2053: "dc_sub None 2053"
  by (dc_eval dc_nc_2053)

lemma dc_nc_2054: "dc_sub None 2054"
  by (dc_eval dc_nc_2054)

lemma dc_nc_2055: "dc_sub None 2055"
  by (dc_eval dc_nc_2055)

lemma dc_nc_2056: "dc_sub None 2056"
  by (dc_eval dc_nc_2056)

lemma dc_nc_2057: "dc_sub None 2057"
  by (dc_eval dc_nc_2057)

lemma dc_nc_2058: "dc_sub None 2058"
  by (dc_eval dc_nc_2058)

lemma dc_nc_2059: "dc_sub None 2059"
  by (dc_eval dc_nc_2059)

lemma dc_nc_2060: "dc_sub None 2060"
  by (dc_eval dc_nc_2060)

lemma dc_nc_2061: "dc_sub None 2061"
  by (dc_eval dc_nc_2061)

lemma dc_nc_2062: "dc_sub None 2062"
  by (dc_eval dc_nc_2062)

lemma dc_nc_2063: "dc_sub None 2063"
  by (dc_eval dc_nc_2063)

lemma upt_nc_128: "[2048..<2064] = [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]"
  by (simp add: upt_rec)

lemma sec_nc_128: "\<forall>j\<in>{16 * 128..<16 * 128 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 128..<16 * 128 + 16}"
  then have "j \<in> set [2048..<2064]" unfolding set_upt by simp
  then have "j \<in> set [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]" unfolding upt_nc_128 .
  then show "dc_sub None j" using dc_nc_2048 dc_nc_2049 dc_nc_2050 dc_nc_2051 dc_nc_2052 dc_nc_2053 dc_nc_2054 dc_nc_2055 dc_nc_2056 dc_nc_2057 dc_nc_2058 dc_nc_2059 dc_nc_2060 dc_nc_2061 dc_nc_2062 dc_nc_2063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
