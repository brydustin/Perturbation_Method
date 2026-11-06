theory GDCX_nc_130
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2080: "gdc_sub None 2080"
  by (gdc_eval gdc_nc_2080)

lemma gdc_nc_2081: "gdc_sub None 2081"
  by (gdc_eval gdc_nc_2081)

lemma gdc_nc_2082: "gdc_sub None 2082"
  by (gdc_eval gdc_nc_2082)

lemma gdc_nc_2083: "gdc_sub None 2083"
  by (gdc_eval gdc_nc_2083)

lemma gdc_nc_2084: "gdc_sub None 2084"
  by (gdc_eval gdc_nc_2084)

lemma gdc_nc_2085: "gdc_sub None 2085"
  by (gdc_eval gdc_nc_2085)

lemma gdc_nc_2086: "gdc_sub None 2086"
  by (gdc_eval gdc_nc_2086)

lemma gdc_nc_2087: "gdc_sub None 2087"
  by (gdc_eval gdc_nc_2087)

lemma gdc_nc_2088: "gdc_sub None 2088"
  by (gdc_eval gdc_nc_2088)

lemma gdc_nc_2089: "gdc_sub None 2089"
  by (gdc_eval gdc_nc_2089)

lemma gdc_nc_2090: "gdc_sub None 2090"
  by (gdc_eval gdc_nc_2090)

lemma gdc_nc_2091: "gdc_sub None 2091"
  by (gdc_eval gdc_nc_2091)

lemma gdc_nc_2092: "gdc_sub None 2092"
  by (gdc_eval gdc_nc_2092)

lemma gdc_nc_2093: "gdc_sub None 2093"
  by (gdc_eval gdc_nc_2093)

lemma gdc_nc_2094: "gdc_sub None 2094"
  by (gdc_eval gdc_nc_2094)

lemma gdc_nc_2095: "gdc_sub None 2095"
  by (gdc_eval gdc_nc_2095)

lemma gupt_nc_130: "[2080..<2096] = [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]"
  by (simp add: upt_rec)

lemma gsec_nc_130: "\<forall>j\<in>{16 * 130..<16 * 130 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 130..<16 * 130 + 16}"
  then have "j \<in> set [2080..<2096]" unfolding set_upt by simp
  then have "j \<in> set [2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095]" unfolding gupt_nc_130 .
  then show "gdc_sub None j" using gdc_nc_2080 gdc_nc_2081 gdc_nc_2082 gdc_nc_2083 gdc_nc_2084 gdc_nc_2085 gdc_nc_2086 gdc_nc_2087 gdc_nc_2088 gdc_nc_2089 gdc_nc_2090 gdc_nc_2091 gdc_nc_2092 gdc_nc_2093 gdc_nc_2094 gdc_nc_2095
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
