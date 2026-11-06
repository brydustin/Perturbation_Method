theory OCX_c30_130
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2080: "oc_sub oc_b30 2080"
  by (oc_eval oc_c30_2080)

lemma oc_c30_2081: "oc_sub oc_b30 2081"
  by (oc_eval oc_c30_2081)

lemma oc_c30_2082: "oc_sub oc_b30 2082"
  by (oc_eval oc_c30_2082)

lemma oc_c30_2083: "oc_sub oc_b30 2083"
  by (oc_eval oc_c30_2083)

lemma oc_c30_2084: "oc_sub oc_b30 2084"
  by (oc_eval oc_c30_2084)

lemma oc_c30_2085: "oc_sub oc_b30 2085"
  by (oc_eval oc_c30_2085)

lemma oc_c30_2086: "oc_sub oc_b30 2086"
  by (oc_eval oc_c30_2086)

lemma oc_c30_2087: "oc_sub oc_b30 2087"
  by (oc_eval oc_c30_2087)

lemma oc_c30_2088: "oc_sub oc_b30 2088"
  by (oc_eval oc_c30_2088)

lemma oc_c30_2089: "oc_sub oc_b30 2089"
  by (oc_eval oc_c30_2089)

lemma oc_c30_2090: "oc_sub oc_b30 2090"
  by (oc_eval oc_c30_2090)

lemma oc_c30_2091: "oc_sub oc_b30 2091"
  by (oc_eval oc_c30_2091)

lemma oc_c30_2092: "oc_sub oc_b30 2092"
  by (oc_eval oc_c30_2092)

lemma oc_c30_2093: "oc_sub oc_b30 2093"
  by (oc_eval oc_c30_2093)

lemma oc_c30_2094: "oc_sub oc_b30 2094"
  by (oc_eval oc_c30_2094)

lemma oc_c30_2095: "oc_sub oc_b30 2095"
  by (oc_eval oc_c30_2095)

lemma upt_c30_130: "[2080..<2096] = [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]"
  by (simp add: upt_rec)

lemma sec_c30_130: "\<forall>j\<in>{16 * 130..<16 * 130 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 130..<16 * 130 + 16}"
  then have "j \<in> set [2080..<2096]" unfolding set_upt by simp
  then have "j \<in> set [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]" unfolding upt_c30_130 .
  then show "oc_sub oc_b30 j" using oc_c30_2080 oc_c30_2081 oc_c30_2082 oc_c30_2083 oc_c30_2084 oc_c30_2085 oc_c30_2086 oc_c30_2087 oc_c30_2088 oc_c30_2089 oc_c30_2090 oc_c30_2091 oc_c30_2092 oc_c30_2093 oc_c30_2094 oc_c30_2095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
