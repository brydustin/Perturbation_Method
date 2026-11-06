theory GDCX_nc_144
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2304: "gdc_sub None 2304"
  by (gdc_eval gdc_nc_2304)

lemma gdc_nc_2305: "gdc_sub None 2305"
  by (gdc_eval gdc_nc_2305)

lemma gdc_nc_2306: "gdc_sub None 2306"
  by (gdc_eval gdc_nc_2306)

lemma gdc_nc_2307: "gdc_sub None 2307"
  by (gdc_eval gdc_nc_2307)

lemma gdc_nc_2308: "gdc_sub None 2308"
  by (gdc_eval gdc_nc_2308)

lemma gdc_nc_2309: "gdc_sub None 2309"
  by (gdc_eval gdc_nc_2309)

lemma gdc_nc_2310: "gdc_sub None 2310"
  by (gdc_eval gdc_nc_2310)

lemma gdc_nc_2311: "gdc_sub None 2311"
  by (gdc_eval gdc_nc_2311)

lemma gdc_nc_2312: "gdc_sub None 2312"
  by (gdc_eval gdc_nc_2312)

lemma gdc_nc_2313: "gdc_sub None 2313"
  by (gdc_eval gdc_nc_2313)

lemma gdc_nc_2314: "gdc_sub None 2314"
  by (gdc_eval gdc_nc_2314)

lemma gdc_nc_2315: "gdc_sub None 2315"
  by (gdc_eval gdc_nc_2315)

lemma gdc_nc_2316: "gdc_sub None 2316"
  by (gdc_eval gdc_nc_2316)

lemma gdc_nc_2317: "gdc_sub None 2317"
  by (gdc_eval gdc_nc_2317)

lemma gdc_nc_2318: "gdc_sub None 2318"
  by (gdc_eval gdc_nc_2318)

lemma gdc_nc_2319: "gdc_sub None 2319"
  by (gdc_eval gdc_nc_2319)

lemma gupt_nc_144: "[2304..<2320] = [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]"
  by (simp add: upt_rec)

lemma gsec_nc_144: "\<forall>j\<in>{16 * 144..<16 * 144 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 144..<16 * 144 + 16}"
  then have "j \<in> set [2304..<2320]" unfolding set_upt by simp
  then have "j \<in> set [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]" unfolding gupt_nc_144 .
  then show "gdc_sub None j" using gdc_nc_2304 gdc_nc_2305 gdc_nc_2306 gdc_nc_2307 gdc_nc_2308 gdc_nc_2309 gdc_nc_2310 gdc_nc_2311 gdc_nc_2312 gdc_nc_2313 gdc_nc_2314 gdc_nc_2315 gdc_nc_2316 gdc_nc_2317 gdc_nc_2318 gdc_nc_2319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
