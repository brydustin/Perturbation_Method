theory DCX_nc_130
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2080: "dc_sub None 2080"
  by (dc_eval dc_nc_2080)

lemma dc_nc_2081: "dc_sub None 2081"
  by (dc_eval dc_nc_2081)

lemma dc_nc_2082: "dc_sub None 2082"
  by (dc_eval dc_nc_2082)

lemma dc_nc_2083: "dc_sub None 2083"
  by (dc_eval dc_nc_2083)

lemma dc_nc_2084: "dc_sub None 2084"
  by (dc_eval dc_nc_2084)

lemma dc_nc_2085: "dc_sub None 2085"
  by (dc_eval dc_nc_2085)

lemma dc_nc_2086: "dc_sub None 2086"
  by (dc_eval dc_nc_2086)

lemma dc_nc_2087: "dc_sub None 2087"
  by (dc_eval dc_nc_2087)

lemma dc_nc_2088: "dc_sub None 2088"
  by (dc_eval dc_nc_2088)

lemma dc_nc_2089: "dc_sub None 2089"
  by (dc_eval dc_nc_2089)

lemma dc_nc_2090: "dc_sub None 2090"
  by (dc_eval dc_nc_2090)

lemma dc_nc_2091: "dc_sub None 2091"
  by (dc_eval dc_nc_2091)

lemma dc_nc_2092: "dc_sub None 2092"
  by (dc_eval dc_nc_2092)

lemma dc_nc_2093: "dc_sub None 2093"
  by (dc_eval dc_nc_2093)

lemma dc_nc_2094: "dc_sub None 2094"
  by (dc_eval dc_nc_2094)

lemma dc_nc_2095: "dc_sub None 2095"
  by (dc_eval dc_nc_2095)

lemma upt_nc_130: "[2080..<2096] = [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]"
  by (simp add: upt_rec)

lemma sec_nc_130: "\<forall>j\<in>{16 * 130..<16 * 130 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 130..<16 * 130 + 16}"
  then have "j \<in> set [2080..<2096]" unfolding set_upt by simp
  then have "j \<in> set [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]" unfolding upt_nc_130 .
  then show "dc_sub None j" using dc_nc_2080 dc_nc_2081 dc_nc_2082 dc_nc_2083 dc_nc_2084 dc_nc_2085 dc_nc_2086 dc_nc_2087 dc_nc_2088 dc_nc_2089 dc_nc_2090 dc_nc_2091 dc_nc_2092 dc_nc_2093 dc_nc_2094 dc_nc_2095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
