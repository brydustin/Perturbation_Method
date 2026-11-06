theory OCX_nc_149
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2384: "oc_sub None 2384"
  by (oc_eval oc_nc_2384)

lemma oc_nc_2385: "oc_sub None 2385"
  by (oc_eval oc_nc_2385)

lemma oc_nc_2386: "oc_sub None 2386"
  by (oc_eval oc_nc_2386)

lemma oc_nc_2387: "oc_sub None 2387"
  by (oc_eval oc_nc_2387)

lemma oc_nc_2388: "oc_sub None 2388"
  by (oc_eval oc_nc_2388)

lemma oc_nc_2389: "oc_sub None 2389"
  by (oc_eval oc_nc_2389)

lemma oc_nc_2390: "oc_sub None 2390"
  by (oc_eval oc_nc_2390)

lemma oc_nc_2391: "oc_sub None 2391"
  by (oc_eval oc_nc_2391)

lemma oc_nc_2392: "oc_sub None 2392"
  by (oc_eval oc_nc_2392)

lemma oc_nc_2393: "oc_sub None 2393"
  by (oc_eval oc_nc_2393)

lemma oc_nc_2394: "oc_sub None 2394"
  by (oc_eval oc_nc_2394)

lemma oc_nc_2395: "oc_sub None 2395"
  by (oc_eval oc_nc_2395)

lemma oc_nc_2396: "oc_sub None 2396"
  by (oc_eval oc_nc_2396)

lemma oc_nc_2397: "oc_sub None 2397"
  by (oc_eval oc_nc_2397)

lemma oc_nc_2398: "oc_sub None 2398"
  by (oc_eval oc_nc_2398)

lemma oc_nc_2399: "oc_sub None 2399"
  by (oc_eval oc_nc_2399)

lemma upt_nc_149: "[2384..<2400] = [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]"
  by (simp add: upt_rec)

lemma sec_nc_149: "\<forall>j\<in>{16 * 149..<16 * 149 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 149..<16 * 149 + 16}"
  then have "j \<in> set [2384..<2400]" unfolding set_upt by simp
  then have "j \<in> set [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]" unfolding upt_nc_149 .
  then show "oc_sub None j" using oc_nc_2384 oc_nc_2385 oc_nc_2386 oc_nc_2387 oc_nc_2388 oc_nc_2389 oc_nc_2390 oc_nc_2391 oc_nc_2392 oc_nc_2393 oc_nc_2394 oc_nc_2395 oc_nc_2396 oc_nc_2397 oc_nc_2398 oc_nc_2399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
