theory OCX_nc_144
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2304: "oc_sub None 2304"
  by (oc_eval oc_nc_2304)

lemma oc_nc_2305: "oc_sub None 2305"
  by (oc_eval oc_nc_2305)

lemma oc_nc_2306: "oc_sub None 2306"
  by (oc_eval oc_nc_2306)

lemma oc_nc_2307: "oc_sub None 2307"
  by (oc_eval oc_nc_2307)

lemma oc_nc_2308: "oc_sub None 2308"
  by (oc_eval oc_nc_2308)

lemma oc_nc_2309: "oc_sub None 2309"
  by (oc_eval oc_nc_2309)

lemma oc_nc_2310: "oc_sub None 2310"
  by (oc_eval oc_nc_2310)

lemma oc_nc_2311: "oc_sub None 2311"
  by (oc_eval oc_nc_2311)

lemma oc_nc_2312: "oc_sub None 2312"
  by (oc_eval oc_nc_2312)

lemma oc_nc_2313: "oc_sub None 2313"
  by (oc_eval oc_nc_2313)

lemma oc_nc_2314: "oc_sub None 2314"
  by (oc_eval oc_nc_2314)

lemma oc_nc_2315: "oc_sub None 2315"
  by (oc_eval oc_nc_2315)

lemma oc_nc_2316: "oc_sub None 2316"
  by (oc_eval oc_nc_2316)

lemma oc_nc_2317: "oc_sub None 2317"
  by (oc_eval oc_nc_2317)

lemma oc_nc_2318: "oc_sub None 2318"
  by (oc_eval oc_nc_2318)

lemma oc_nc_2319: "oc_sub None 2319"
  by (oc_eval oc_nc_2319)

lemma upt_nc_144: "[2304..<2320] = [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]"
  by (simp add: upt_rec)

lemma sec_nc_144: "\<forall>j\<in>{16 * 144..<16 * 144 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 144..<16 * 144 + 16}"
  then have "j \<in> set [2304..<2320]" unfolding set_upt by simp
  then have "j \<in> set [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]" unfolding upt_nc_144 .
  then show "oc_sub None j" using oc_nc_2304 oc_nc_2305 oc_nc_2306 oc_nc_2307 oc_nc_2308 oc_nc_2309 oc_nc_2310 oc_nc_2311 oc_nc_2312 oc_nc_2313 oc_nc_2314 oc_nc_2315 oc_nc_2316 oc_nc_2317 oc_nc_2318 oc_nc_2319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
