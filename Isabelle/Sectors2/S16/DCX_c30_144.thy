theory DCX_c30_144
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2304: "dc_sub dc_b30 2304"
  by (dc_eval dc_c30_2304)

lemma dc_c30_2305: "dc_sub dc_b30 2305"
  by (dc_eval dc_c30_2305)

lemma dc_c30_2306: "dc_sub dc_b30 2306"
  by (dc_eval dc_c30_2306)

lemma dc_c30_2307: "dc_sub dc_b30 2307"
  by (dc_eval dc_c30_2307)

lemma dc_c30_2308: "dc_sub dc_b30 2308"
  by (dc_eval dc_c30_2308)

lemma dc_c30_2309: "dc_sub dc_b30 2309"
  by (dc_eval dc_c30_2309)

lemma dc_c30_2310: "dc_sub dc_b30 2310"
  by (dc_eval dc_c30_2310)

lemma dc_c30_2311: "dc_sub dc_b30 2311"
  by (dc_eval dc_c30_2311)

lemma dc_c30_2312: "dc_sub dc_b30 2312"
  by (dc_eval dc_c30_2312)

lemma dc_c30_2313: "dc_sub dc_b30 2313"
  by (dc_eval dc_c30_2313)

lemma dc_c30_2314: "dc_sub dc_b30 2314"
  by (dc_eval dc_c30_2314)

lemma dc_c30_2315: "dc_sub dc_b30 2315"
  by (dc_eval dc_c30_2315)

lemma dc_c30_2316: "dc_sub dc_b30 2316"
  by (dc_eval dc_c30_2316)

lemma dc_c30_2317: "dc_sub dc_b30 2317"
  by (dc_eval dc_c30_2317)

lemma dc_c30_2318: "dc_sub dc_b30 2318"
  by (dc_eval dc_c30_2318)

lemma dc_c30_2319: "dc_sub dc_b30 2319"
  by (dc_eval dc_c30_2319)

lemma upt_c30_144: "[2304..<2320] = [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]"
  by (simp add: upt_rec)

lemma sec_c30_144: "\<forall>j\<in>{16 * 144..<16 * 144 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 144..<16 * 144 + 16}"
  then have "j \<in> set [2304..<2320]" unfolding set_upt by simp
  then have "j \<in> set [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]" unfolding upt_c30_144 .
  then show "dc_sub dc_b30 j" using dc_c30_2304 dc_c30_2305 dc_c30_2306 dc_c30_2307 dc_c30_2308 dc_c30_2309 dc_c30_2310 dc_c30_2311 dc_c30_2312 dc_c30_2313 dc_c30_2314 dc_c30_2315 dc_c30_2316 dc_c30_2317 dc_c30_2318 dc_c30_2319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
