theory OCX_c30_128
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2048: "oc_sub oc_b30 2048"
  by (oc_eval oc_c30_2048)

lemma oc_c30_2049: "oc_sub oc_b30 2049"
  by (oc_eval oc_c30_2049)

lemma oc_c30_2050: "oc_sub oc_b30 2050"
  by (oc_eval oc_c30_2050)

lemma oc_c30_2051: "oc_sub oc_b30 2051"
  by (oc_eval oc_c30_2051)

lemma oc_c30_2052: "oc_sub oc_b30 2052"
  by (oc_eval oc_c30_2052)

lemma oc_c30_2053: "oc_sub oc_b30 2053"
  by (oc_eval oc_c30_2053)

lemma oc_c30_2054: "oc_sub oc_b30 2054"
  by (oc_eval oc_c30_2054)

lemma oc_c30_2055: "oc_sub oc_b30 2055"
  by (oc_eval oc_c30_2055)

lemma oc_c30_2056: "oc_sub oc_b30 2056"
  by (oc_eval oc_c30_2056)

lemma oc_c30_2057: "oc_sub oc_b30 2057"
  by (oc_eval oc_c30_2057)

lemma oc_c30_2058: "oc_sub oc_b30 2058"
  by (oc_eval oc_c30_2058)

lemma oc_c30_2059: "oc_sub oc_b30 2059"
  by (oc_eval oc_c30_2059)

lemma oc_c30_2060: "oc_sub oc_b30 2060"
  by (oc_eval oc_c30_2060)

lemma oc_c30_2061: "oc_sub oc_b30 2061"
  by (oc_eval oc_c30_2061)

lemma oc_c30_2062: "oc_sub oc_b30 2062"
  by (oc_eval oc_c30_2062)

lemma oc_c30_2063: "oc_sub oc_b30 2063"
  by (oc_eval oc_c30_2063)

lemma upt_c30_128: "[2048..<2064] = [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]"
  by (simp add: upt_rec)

lemma sec_c30_128: "\<forall>j\<in>{16 * 128..<16 * 128 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 128..<16 * 128 + 16}"
  then have "j \<in> set [2048..<2064]" unfolding set_upt by simp
  then have "j \<in> set [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063]" unfolding upt_c30_128 .
  then show "oc_sub oc_b30 j" using oc_c30_2048 oc_c30_2049 oc_c30_2050 oc_c30_2051 oc_c30_2052 oc_c30_2053 oc_c30_2054 oc_c30_2055 oc_c30_2056 oc_c30_2057 oc_c30_2058 oc_c30_2059 oc_c30_2060 oc_c30_2061 oc_c30_2062 oc_c30_2063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
