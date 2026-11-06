theory DCX_c30_147
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2352: "dc_sub dc_b30 2352"
  by (dc_eval dc_c30_2352)

lemma dc_c30_2353: "dc_sub dc_b30 2353"
  by (dc_eval dc_c30_2353)

lemma dc_c30_2354: "dc_sub dc_b30 2354"
  by (dc_eval dc_c30_2354)

lemma dc_c30_2355: "dc_sub dc_b30 2355"
  by (dc_eval dc_c30_2355)

lemma dc_c30_2356: "dc_sub dc_b30 2356"
  by (dc_eval dc_c30_2356)

lemma dc_c30_2357: "dc_sub dc_b30 2357"
  by (dc_eval dc_c30_2357)

lemma dc_c30_2358: "dc_sub dc_b30 2358"
  by (dc_eval dc_c30_2358)

lemma dc_c30_2359: "dc_sub dc_b30 2359"
  by (dc_eval dc_c30_2359)

lemma dc_c30_2360: "dc_sub dc_b30 2360"
  by (dc_eval dc_c30_2360)

lemma dc_c30_2361: "dc_sub dc_b30 2361"
  by (dc_eval dc_c30_2361)

lemma dc_c30_2362: "dc_sub dc_b30 2362"
  by (dc_eval dc_c30_2362)

lemma dc_c30_2363: "dc_sub dc_b30 2363"
  by (dc_eval dc_c30_2363)

lemma dc_c30_2364: "dc_sub dc_b30 2364"
  by (dc_eval dc_c30_2364)

lemma dc_c30_2365: "dc_sub dc_b30 2365"
  by (dc_eval dc_c30_2365)

lemma dc_c30_2366: "dc_sub dc_b30 2366"
  by (dc_eval dc_c30_2366)

lemma dc_c30_2367: "dc_sub dc_b30 2367"
  by (dc_eval dc_c30_2367)

lemma upt_c30_147: "[2352..<2368] = [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]"
  by (simp add: upt_rec)

lemma sec_c30_147: "\<forall>j\<in>{16 * 147..<16 * 147 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 147..<16 * 147 + 16}"
  then have "j \<in> set [2352..<2368]" unfolding set_upt by simp
  then have "j \<in> set [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]" unfolding upt_c30_147 .
  then show "dc_sub dc_b30 j" using dc_c30_2352 dc_c30_2353 dc_c30_2354 dc_c30_2355 dc_c30_2356 dc_c30_2357 dc_c30_2358 dc_c30_2359 dc_c30_2360 dc_c30_2361 dc_c30_2362 dc_c30_2363 dc_c30_2364 dc_c30_2365 dc_c30_2366 dc_c30_2367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
