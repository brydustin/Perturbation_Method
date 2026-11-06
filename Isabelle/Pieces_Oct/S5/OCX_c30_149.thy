theory OCX_c30_149
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2384: "oc_sub oc_b30 2384"
  by (oc_eval oc_c30_2384)

lemma oc_c30_2385: "oc_sub oc_b30 2385"
  by (oc_eval oc_c30_2385)

lemma oc_c30_2386: "oc_sub oc_b30 2386"
  by (oc_eval oc_c30_2386)

lemma oc_c30_2387: "oc_sub oc_b30 2387"
  by (oc_eval oc_c30_2387)

lemma oc_c30_2388: "oc_sub oc_b30 2388"
  by (oc_eval oc_c30_2388)

lemma oc_c30_2389: "oc_sub oc_b30 2389"
  by (oc_eval oc_c30_2389)

lemma oc_c30_2390: "oc_sub oc_b30 2390"
  by (oc_eval oc_c30_2390)

lemma oc_c30_2391: "oc_sub oc_b30 2391"
  by (oc_eval oc_c30_2391)

lemma oc_c30_2392: "oc_sub oc_b30 2392"
  by (oc_eval oc_c30_2392)

lemma oc_c30_2393: "oc_sub oc_b30 2393"
  by (oc_eval oc_c30_2393)

lemma oc_c30_2394: "oc_sub oc_b30 2394"
  by (oc_eval oc_c30_2394)

lemma oc_c30_2395: "oc_sub oc_b30 2395"
  by (oc_eval oc_c30_2395)

lemma oc_c30_2396: "oc_sub oc_b30 2396"
  by (oc_eval oc_c30_2396)

lemma oc_c30_2397: "oc_sub oc_b30 2397"
  by (oc_eval oc_c30_2397)

lemma oc_c30_2398: "oc_sub oc_b30 2398"
  by (oc_eval oc_c30_2398)

lemma oc_c30_2399: "oc_sub oc_b30 2399"
  by (oc_eval oc_c30_2399)

lemma upt_c30_149: "[2384..<2400] = [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]"
  by (simp add: upt_rec)

lemma sec_c30_149: "\<forall>j\<in>{16 * 149..<16 * 149 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 149..<16 * 149 + 16}"
  then have "j \<in> set [2384..<2400]" unfolding set_upt by simp
  then have "j \<in> set [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]" unfolding upt_c30_149 .
  then show "oc_sub oc_b30 j" using oc_c30_2384 oc_c30_2385 oc_c30_2386 oc_c30_2387 oc_c30_2388 oc_c30_2389 oc_c30_2390 oc_c30_2391 oc_c30_2392 oc_c30_2393 oc_c30_2394 oc_c30_2395 oc_c30_2396 oc_c30_2397 oc_c30_2398 oc_c30_2399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
