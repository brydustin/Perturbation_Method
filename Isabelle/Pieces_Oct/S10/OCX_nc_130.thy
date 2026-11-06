theory OCX_nc_130
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2080: "oc_sub None 2080"
  by (oc_eval oc_nc_2080)

lemma oc_nc_2081: "oc_sub None 2081"
  by (oc_eval oc_nc_2081)

lemma oc_nc_2082: "oc_sub None 2082"
  by (oc_eval oc_nc_2082)

lemma oc_nc_2083: "oc_sub None 2083"
  by (oc_eval oc_nc_2083)

lemma oc_nc_2084: "oc_sub None 2084"
  by (oc_eval oc_nc_2084)

lemma oc_nc_2085: "oc_sub None 2085"
  by (oc_eval oc_nc_2085)

lemma oc_nc_2086: "oc_sub None 2086"
  by (oc_eval oc_nc_2086)

lemma oc_nc_2087: "oc_sub None 2087"
  by (oc_eval oc_nc_2087)

lemma oc_nc_2088: "oc_sub None 2088"
  by (oc_eval oc_nc_2088)

lemma oc_nc_2089: "oc_sub None 2089"
  by (oc_eval oc_nc_2089)

lemma oc_nc_2090: "oc_sub None 2090"
  by (oc_eval oc_nc_2090)

lemma oc_nc_2091: "oc_sub None 2091"
  by (oc_eval oc_nc_2091)

lemma oc_nc_2092: "oc_sub None 2092"
  by (oc_eval oc_nc_2092)

lemma oc_nc_2093: "oc_sub None 2093"
  by (oc_eval oc_nc_2093)

lemma oc_nc_2094: "oc_sub None 2094"
  by (oc_eval oc_nc_2094)

lemma oc_nc_2095: "oc_sub None 2095"
  by (oc_eval oc_nc_2095)

lemma upt_nc_130: "[2080..<2096] = [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]"
  by (simp add: upt_rec)

lemma sec_nc_130: "\<forall>j\<in>{16 * 130..<16 * 130 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 130..<16 * 130 + 16}"
  then have "j \<in> set [2080..<2096]" unfolding set_upt by simp
  then have "j \<in> set [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]" unfolding upt_nc_130 .
  then show "oc_sub None j" using oc_nc_2080 oc_nc_2081 oc_nc_2082 oc_nc_2083 oc_nc_2084 oc_nc_2085 oc_nc_2086 oc_nc_2087 oc_nc_2088 oc_nc_2089 oc_nc_2090 oc_nc_2091 oc_nc_2092 oc_nc_2093 oc_nc_2094 oc_nc_2095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
