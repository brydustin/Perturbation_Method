theory DCX_c30_130
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2080: "dc_sub dc_b30 2080"
  by (dc_eval dc_c30_2080)

lemma dc_c30_2081: "dc_sub dc_b30 2081"
  by (dc_eval dc_c30_2081)

lemma dc_c30_2082: "dc_sub dc_b30 2082"
  by (dc_eval dc_c30_2082)

lemma dc_c30_2083: "dc_sub dc_b30 2083"
  by (dc_eval dc_c30_2083)

lemma dc_c30_2084: "dc_sub dc_b30 2084"
  by (dc_eval dc_c30_2084)

lemma dc_c30_2085: "dc_sub dc_b30 2085"
  by (dc_eval dc_c30_2085)

lemma dc_c30_2086: "dc_sub dc_b30 2086"
  by (dc_eval dc_c30_2086)

lemma dc_c30_2087: "dc_sub dc_b30 2087"
  by (dc_eval dc_c30_2087)

lemma dc_c30_2088: "dc_sub dc_b30 2088"
  by (dc_eval dc_c30_2088)

lemma dc_c30_2089: "dc_sub dc_b30 2089"
  by (dc_eval dc_c30_2089)

lemma dc_c30_2090: "dc_sub dc_b30 2090"
  by (dc_eval dc_c30_2090)

lemma dc_c30_2091: "dc_sub dc_b30 2091"
  by (dc_eval dc_c30_2091)

lemma dc_c30_2092: "dc_sub dc_b30 2092"
  by (dc_eval dc_c30_2092)

lemma dc_c30_2093: "dc_sub dc_b30 2093"
  by (dc_eval dc_c30_2093)

lemma dc_c30_2094: "dc_sub dc_b30 2094"
  by (dc_eval dc_c30_2094)

lemma dc_c30_2095: "dc_sub dc_b30 2095"
  by (dc_eval dc_c30_2095)

lemma upt_c30_130: "[2080..<2096] = [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]"
  by (simp add: upt_rec)

lemma sec_c30_130: "\<forall>j\<in>{16 * 130..<16 * 130 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 130..<16 * 130 + 16}"
  then have "j \<in> set [2080..<2096]" unfolding set_upt by simp
  then have "j \<in> set [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]" unfolding upt_c30_130 .
  then show "dc_sub dc_b30 j" using dc_c30_2080 dc_c30_2081 dc_c30_2082 dc_c30_2083 dc_c30_2084 dc_c30_2085 dc_c30_2086 dc_c30_2087 dc_c30_2088 dc_c30_2089 dc_c30_2090 dc_c30_2091 dc_c30_2092 dc_c30_2093 dc_c30_2094 dc_c30_2095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
