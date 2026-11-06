theory GOCX_nc_128
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2048: "goc_sub None 2048"
  by (goc_eval goc_nc_2048)

lemma goc_nc_2049: "goc_sub None 2049"
  by (goc_eval goc_nc_2049)

lemma goc_nc_2050: "goc_sub None 2050"
  by (goc_eval goc_nc_2050)

lemma goc_nc_2051: "goc_sub None 2051"
  by (goc_eval goc_nc_2051)

lemma goc_nc_2052: "goc_sub None 2052"
  by (goc_eval goc_nc_2052)

lemma goc_nc_2053: "goc_sub None 2053"
  by (goc_eval goc_nc_2053)

lemma goc_nc_2054: "goc_sub None 2054"
  by (goc_eval goc_nc_2054)

lemma goc_nc_2055: "goc_sub None 2055"
  by (goc_eval goc_nc_2055)

lemma goc_nc_2056: "goc_sub None 2056"
  by (goc_eval goc_nc_2056)

lemma goc_nc_2057: "goc_sub None 2057"
  by (goc_eval goc_nc_2057)

lemma goc_nc_2058: "goc_sub None 2058"
  by (goc_eval goc_nc_2058)

lemma goc_nc_2059: "goc_sub None 2059"
  by (goc_eval goc_nc_2059)

lemma goc_nc_2060: "goc_sub None 2060"
  by (goc_eval goc_nc_2060)

lemma goc_nc_2061: "goc_sub None 2061"
  by (goc_eval goc_nc_2061)

lemma goc_nc_2062: "goc_sub None 2062"
  by (goc_eval goc_nc_2062)

lemma goc_nc_2063: "goc_sub None 2063"
  by (goc_eval goc_nc_2063)

lemma gupt_nc_128: "[2048..<2064] = [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]"
  by (simp add: upt_rec)

lemma gsec_nc_128: "\<forall>j\<in>{16 * 128..<16 * 128 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 128..<16 * 128 + 16}"
  then have "j \<in> set [2048..<2064]" unfolding set_upt by simp
  then have "j \<in> set [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]" unfolding gupt_nc_128 .
  then show "goc_sub None j" using goc_nc_2048 goc_nc_2049 goc_nc_2050 goc_nc_2051 goc_nc_2052 goc_nc_2053 goc_nc_2054 goc_nc_2055 goc_nc_2056 goc_nc_2057 goc_nc_2058 goc_nc_2059 goc_nc_2060 goc_nc_2061 goc_nc_2062 goc_nc_2063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
