theory DCX_nc_144
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2304: "dc_sub None 2304"
  by (dc_eval dc_nc_2304)

lemma dc_nc_2305: "dc_sub None 2305"
  by (dc_eval dc_nc_2305)

lemma dc_nc_2306: "dc_sub None 2306"
  by (dc_eval dc_nc_2306)

lemma dc_nc_2307: "dc_sub None 2307"
  by (dc_eval dc_nc_2307)

lemma dc_nc_2308: "dc_sub None 2308"
  by (dc_eval dc_nc_2308)

lemma dc_nc_2309: "dc_sub None 2309"
  by (dc_eval dc_nc_2309)

lemma dc_nc_2310: "dc_sub None 2310"
  by (dc_eval dc_nc_2310)

lemma dc_nc_2311: "dc_sub None 2311"
  by (dc_eval dc_nc_2311)

lemma dc_nc_2312: "dc_sub None 2312"
  by (dc_eval dc_nc_2312)

lemma dc_nc_2313: "dc_sub None 2313"
  by (dc_eval dc_nc_2313)

lemma dc_nc_2314: "dc_sub None 2314"
  by (dc_eval dc_nc_2314)

lemma dc_nc_2315: "dc_sub None 2315"
  by (dc_eval dc_nc_2315)

lemma dc_nc_2316: "dc_sub None 2316"
  by (dc_eval dc_nc_2316)

lemma dc_nc_2317: "dc_sub None 2317"
  by (dc_eval dc_nc_2317)

lemma dc_nc_2318: "dc_sub None 2318"
  by (dc_eval dc_nc_2318)

lemma dc_nc_2319: "dc_sub None 2319"
  by (dc_eval dc_nc_2319)

lemma upt_nc_144: "[2304..<2320] = [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]"
  by (simp add: upt_rec)

lemma sec_nc_144: "\<forall>j\<in>{16 * 144..<16 * 144 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 144..<16 * 144 + 16}"
  then have "j \<in> set [2304..<2320]" unfolding set_upt by simp
  then have "j \<in> set [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]" unfolding upt_nc_144 .
  then show "dc_sub None j" using dc_nc_2304 dc_nc_2305 dc_nc_2306 dc_nc_2307 dc_nc_2308 dc_nc_2309 dc_nc_2310 dc_nc_2311 dc_nc_2312 dc_nc_2313 dc_nc_2314 dc_nc_2315 dc_nc_2316 dc_nc_2317 dc_nc_2318 dc_nc_2319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
