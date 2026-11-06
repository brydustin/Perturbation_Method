theory GOCX_nc_144
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2304: "goc_sub None 2304"
  by (goc_eval goc_nc_2304)

lemma goc_nc_2305: "goc_sub None 2305"
  by (goc_eval goc_nc_2305)

lemma goc_nc_2306: "goc_sub None 2306"
  by (goc_eval goc_nc_2306)

lemma goc_nc_2307: "goc_sub None 2307"
  by (goc_eval goc_nc_2307)

lemma goc_nc_2308: "goc_sub None 2308"
  by (goc_eval goc_nc_2308)

lemma goc_nc_2309: "goc_sub None 2309"
  by (goc_eval goc_nc_2309)

lemma goc_nc_2310: "goc_sub None 2310"
  by (goc_eval goc_nc_2310)

lemma goc_nc_2311: "goc_sub None 2311"
  by (goc_eval goc_nc_2311)

lemma goc_nc_2312: "goc_sub None 2312"
  by (goc_eval goc_nc_2312)

lemma goc_nc_2313: "goc_sub None 2313"
  by (goc_eval goc_nc_2313)

lemma goc_nc_2314: "goc_sub None 2314"
  by (goc_eval goc_nc_2314)

lemma goc_nc_2315: "goc_sub None 2315"
  by (goc_eval goc_nc_2315)

lemma goc_nc_2316: "goc_sub None 2316"
  by (goc_eval goc_nc_2316)

lemma goc_nc_2317: "goc_sub None 2317"
  by (goc_eval goc_nc_2317)

lemma goc_nc_2318: "goc_sub None 2318"
  by (goc_eval goc_nc_2318)

lemma goc_nc_2319: "goc_sub None 2319"
  by (goc_eval goc_nc_2319)

lemma gupt_nc_144: "[2304..<2320] = [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]"
  by (simp add: upt_rec)

lemma gsec_nc_144: "\<forall>j\<in>{16 * 144..<16 * 144 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 144..<16 * 144 + 16}"
  then have "j \<in> set [2304..<2320]" unfolding set_upt by simp
  then have "j \<in> set [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]" unfolding gupt_nc_144 .
  then show "goc_sub None j" using goc_nc_2304 goc_nc_2305 goc_nc_2306 goc_nc_2307 goc_nc_2308 goc_nc_2309 goc_nc_2310 goc_nc_2311 goc_nc_2312 goc_nc_2313 goc_nc_2314 goc_nc_2315 goc_nc_2316 goc_nc_2317 goc_nc_2318 goc_nc_2319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
