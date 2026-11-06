theory OCX_nc_128
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2048: "oc_sub None 2048"
  by (oc_eval oc_nc_2048)

lemma oc_nc_2049: "oc_sub None 2049"
  by (oc_eval oc_nc_2049)

lemma oc_nc_2050: "oc_sub None 2050"
  by (oc_eval oc_nc_2050)

lemma oc_nc_2051: "oc_sub None 2051"
  by (oc_eval oc_nc_2051)

lemma oc_nc_2052: "oc_sub None 2052"
  by (oc_eval oc_nc_2052)

lemma oc_nc_2053: "oc_sub None 2053"
  by (oc_eval oc_nc_2053)

lemma oc_nc_2054: "oc_sub None 2054"
  by (oc_eval oc_nc_2054)

lemma oc_nc_2055: "oc_sub None 2055"
  by (oc_eval oc_nc_2055)

lemma oc_nc_2056: "oc_sub None 2056"
  by (oc_eval oc_nc_2056)

lemma oc_nc_2057: "oc_sub None 2057"
  by (oc_eval oc_nc_2057)

lemma oc_nc_2058: "oc_sub None 2058"
  by (oc_eval oc_nc_2058)

lemma oc_nc_2059: "oc_sub None 2059"
  by (oc_eval oc_nc_2059)

lemma oc_nc_2060: "oc_sub None 2060"
  by (oc_eval oc_nc_2060)

lemma oc_nc_2061: "oc_sub None 2061"
  by (oc_eval oc_nc_2061)

lemma oc_nc_2062: "oc_sub None 2062"
  by (oc_eval oc_nc_2062)

lemma oc_nc_2063: "oc_sub None 2063"
  by (oc_eval oc_nc_2063)

lemma upt_nc_128: "[2048..<2064] = [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]"
  by (simp add: upt_rec)

lemma sec_nc_128: "\<forall>j\<in>{16 * 128..<16 * 128 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 128..<16 * 128 + 16}"
  then have "j \<in> set [2048..<2064]" unfolding set_upt by simp
  then have "j \<in> set [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]" unfolding upt_nc_128 .
  then show "oc_sub None j" using oc_nc_2048 oc_nc_2049 oc_nc_2050 oc_nc_2051 oc_nc_2052 oc_nc_2053 oc_nc_2054 oc_nc_2055 oc_nc_2056 oc_nc_2057 oc_nc_2058 oc_nc_2059 oc_nc_2060 oc_nc_2061 oc_nc_2062 oc_nc_2063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
