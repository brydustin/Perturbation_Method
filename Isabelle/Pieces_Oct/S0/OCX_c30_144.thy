theory OCX_c30_144
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2304: "oc_sub oc_b30 2304"
  by (oc_eval oc_c30_2304)

lemma oc_c30_2305: "oc_sub oc_b30 2305"
  by (oc_eval oc_c30_2305)

lemma oc_c30_2306: "oc_sub oc_b30 2306"
  by (oc_eval oc_c30_2306)

lemma oc_c30_2307: "oc_sub oc_b30 2307"
  by (oc_eval oc_c30_2307)

lemma oc_c30_2308: "oc_sub oc_b30 2308"
  by (oc_eval oc_c30_2308)

lemma oc_c30_2309: "oc_sub oc_b30 2309"
  by (oc_eval oc_c30_2309)

lemma oc_c30_2310: "oc_sub oc_b30 2310"
  by (oc_eval oc_c30_2310)

lemma oc_c30_2311: "oc_sub oc_b30 2311"
  by (oc_eval oc_c30_2311)

lemma oc_c30_2312: "oc_sub oc_b30 2312"
  by (oc_eval oc_c30_2312)

lemma oc_c30_2313: "oc_sub oc_b30 2313"
  by (oc_eval oc_c30_2313)

lemma oc_c30_2314: "oc_sub oc_b30 2314"
  by (oc_eval oc_c30_2314)

lemma oc_c30_2315: "oc_sub oc_b30 2315"
  by (oc_eval oc_c30_2315)

lemma oc_c30_2316: "oc_sub oc_b30 2316"
  by (oc_eval oc_c30_2316)

lemma oc_c30_2317: "oc_sub oc_b30 2317"
  by (oc_eval oc_c30_2317)

lemma oc_c30_2318: "oc_sub oc_b30 2318"
  by (oc_eval oc_c30_2318)

lemma oc_c30_2319: "oc_sub oc_b30 2319"
  by (oc_eval oc_c30_2319)

lemma upt_c30_144: "[2304..<2320] = [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]"
  by (simp add: upt_rec)

lemma sec_c30_144: "\<forall>j\<in>{16 * 144..<16 * 144 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 144..<16 * 144 + 16}"
  then have "j \<in> set [2304..<2320]" unfolding set_upt by simp
  then have "j \<in> set [2304, 2305, 2306, 2307, 2308, 2309, 2310, 2311, 2312, 2313, 2314, 2315, 2316, 2317, 2318, 2319]" unfolding upt_c30_144 .
  then show "oc_sub oc_b30 j" using oc_c30_2304 oc_c30_2305 oc_c30_2306 oc_c30_2307 oc_c30_2308 oc_c30_2309 oc_c30_2310 oc_c30_2311 oc_c30_2312 oc_c30_2313 oc_c30_2314 oc_c30_2315 oc_c30_2316 oc_c30_2317 oc_c30_2318 oc_c30_2319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
