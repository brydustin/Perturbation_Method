theory DCX_nc_149
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2384: "dc_sub None 2384"
  by (dc_eval dc_nc_2384)

lemma dc_nc_2385: "dc_sub None 2385"
  by (dc_eval dc_nc_2385)

lemma dc_nc_2386: "dc_sub None 2386"
  by (dc_eval dc_nc_2386)

lemma dc_nc_2387: "dc_sub None 2387"
  by (dc_eval dc_nc_2387)

lemma dc_nc_2388: "dc_sub None 2388"
  by (dc_eval dc_nc_2388)

lemma dc_nc_2389: "dc_sub None 2389"
  by (dc_eval dc_nc_2389)

lemma dc_nc_2390: "dc_sub None 2390"
  by (dc_eval dc_nc_2390)

lemma dc_nc_2391: "dc_sub None 2391"
  by (dc_eval dc_nc_2391)

lemma dc_nc_2392: "dc_sub None 2392"
  by (dc_eval dc_nc_2392)

lemma dc_nc_2393: "dc_sub None 2393"
  by (dc_eval dc_nc_2393)

lemma dc_nc_2394: "dc_sub None 2394"
  by (dc_eval dc_nc_2394)

lemma dc_nc_2395: "dc_sub None 2395"
  by (dc_eval dc_nc_2395)

lemma dc_nc_2396: "dc_sub None 2396"
  by (dc_eval dc_nc_2396)

lemma dc_nc_2397: "dc_sub None 2397"
  by (dc_eval dc_nc_2397)

lemma dc_nc_2398: "dc_sub None 2398"
  by (dc_eval dc_nc_2398)

lemma dc_nc_2399: "dc_sub None 2399"
  by (dc_eval dc_nc_2399)

lemma upt_nc_149: "[2384..<2400] = [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]"
  by (simp add: upt_rec)

lemma sec_nc_149: "\<forall>j\<in>{16 * 149..<16 * 149 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 149..<16 * 149 + 16}"
  then have "j \<in> set [2384..<2400]" unfolding set_upt by simp
  then have "j \<in> set [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]" unfolding upt_nc_149 .
  then show "dc_sub None j" using dc_nc_2384 dc_nc_2385 dc_nc_2386 dc_nc_2387 dc_nc_2388 dc_nc_2389 dc_nc_2390 dc_nc_2391 dc_nc_2392 dc_nc_2393 dc_nc_2394 dc_nc_2395 dc_nc_2396 dc_nc_2397 dc_nc_2398 dc_nc_2399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
