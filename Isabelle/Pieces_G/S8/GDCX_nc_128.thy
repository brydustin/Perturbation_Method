theory GDCX_nc_128
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2048: "gdc_sub None 2048"
  by (gdc_eval gdc_nc_2048)

lemma gdc_nc_2049: "gdc_sub None 2049"
  by (gdc_eval gdc_nc_2049)

lemma gdc_nc_2050: "gdc_sub None 2050"
  by (gdc_eval gdc_nc_2050)

lemma gdc_nc_2051: "gdc_sub None 2051"
  by (gdc_eval gdc_nc_2051)

lemma gdc_nc_2052: "gdc_sub None 2052"
  by (gdc_eval gdc_nc_2052)

lemma gdc_nc_2053: "gdc_sub None 2053"
  by (gdc_eval gdc_nc_2053)

lemma gdc_nc_2054: "gdc_sub None 2054"
  by (gdc_eval gdc_nc_2054)

lemma gdc_nc_2055: "gdc_sub None 2055"
  by (gdc_eval gdc_nc_2055)

lemma gdc_nc_2056: "gdc_sub None 2056"
  by (gdc_eval gdc_nc_2056)

lemma gdc_nc_2057: "gdc_sub None 2057"
  by (gdc_eval gdc_nc_2057)

lemma gdc_nc_2058: "gdc_sub None 2058"
  by (gdc_eval gdc_nc_2058)

lemma gdc_nc_2059: "gdc_sub None 2059"
  by (gdc_eval gdc_nc_2059)

lemma gdc_nc_2060: "gdc_sub None 2060"
  by (gdc_eval gdc_nc_2060)

lemma gdc_nc_2061: "gdc_sub None 2061"
  by (gdc_eval gdc_nc_2061)

lemma gdc_nc_2062: "gdc_sub None 2062"
  by (gdc_eval gdc_nc_2062)

lemma gdc_nc_2063: "gdc_sub None 2063"
  by (gdc_eval gdc_nc_2063)

lemma gupt_nc_128: "[2048..<2064] = [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]"
  by (simp add: upt_rec)

lemma gsec_nc_128: "\<forall>j\<in>{16 * 128..<16 * 128 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 128..<16 * 128 + 16}"
  then have "j \<in> set [2048..<2064]" unfolding set_upt by simp
  then have "j \<in> set [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]" unfolding gupt_nc_128 .
  then show "gdc_sub None j" using gdc_nc_2048 gdc_nc_2049 gdc_nc_2050 gdc_nc_2051 gdc_nc_2052 gdc_nc_2053 gdc_nc_2054 gdc_nc_2055 gdc_nc_2056 gdc_nc_2057 gdc_nc_2058 gdc_nc_2059 gdc_nc_2060 gdc_nc_2061 gdc_nc_2062 gdc_nc_2063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
