theory GOCX_nc_130
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2080: "goc_sub None 2080"
  by (goc_eval goc_nc_2080)

lemma goc_nc_2081: "goc_sub None 2081"
  by (goc_eval goc_nc_2081)

lemma goc_nc_2082: "goc_sub None 2082"
  by (goc_eval goc_nc_2082)

lemma goc_nc_2083: "goc_sub None 2083"
  by (goc_eval goc_nc_2083)

lemma goc_nc_2084: "goc_sub None 2084"
  by (goc_eval goc_nc_2084)

lemma goc_nc_2085: "goc_sub None 2085"
  by (goc_eval goc_nc_2085)

lemma goc_nc_2086: "goc_sub None 2086"
  by (goc_eval goc_nc_2086)

lemma goc_nc_2087: "goc_sub None 2087"
  by (goc_eval goc_nc_2087)

lemma goc_nc_2088: "goc_sub None 2088"
  by (goc_eval goc_nc_2088)

lemma goc_nc_2089: "goc_sub None 2089"
  by (goc_eval goc_nc_2089)

lemma goc_nc_2090: "goc_sub None 2090"
  by (goc_eval goc_nc_2090)

lemma goc_nc_2091: "goc_sub None 2091"
  by (goc_eval goc_nc_2091)

lemma goc_nc_2092: "goc_sub None 2092"
  by (goc_eval goc_nc_2092)

lemma goc_nc_2093: "goc_sub None 2093"
  by (goc_eval goc_nc_2093)

lemma goc_nc_2094: "goc_sub None 2094"
  by (goc_eval goc_nc_2094)

lemma goc_nc_2095: "goc_sub None 2095"
  by (goc_eval goc_nc_2095)

lemma gupt_nc_130: "[2080..<2096] = [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]"
  by (simp add: upt_rec)

lemma gsec_nc_130: "\<forall>j\<in>{16 * 130..<16 * 130 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 130..<16 * 130 + 16}"
  then have "j \<in> set [2080..<2096]" unfolding set_upt by simp
  then have "j \<in> set [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]" unfolding gupt_nc_130 .
  then show "goc_sub None j" using goc_nc_2080 goc_nc_2081 goc_nc_2082 goc_nc_2083 goc_nc_2084 goc_nc_2085 goc_nc_2086 goc_nc_2087 goc_nc_2088 goc_nc_2089 goc_nc_2090 goc_nc_2091 goc_nc_2092 goc_nc_2093 goc_nc_2094 goc_nc_2095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
