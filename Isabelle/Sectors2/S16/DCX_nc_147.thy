theory DCX_nc_147
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2352: "dc_sub None 2352"
  by (dc_eval dc_nc_2352)

lemma dc_nc_2353: "dc_sub None 2353"
  by (dc_eval dc_nc_2353)

lemma dc_nc_2354: "dc_sub None 2354"
  by (dc_eval dc_nc_2354)

lemma dc_nc_2355: "dc_sub None 2355"
  by (dc_eval dc_nc_2355)

lemma dc_nc_2356: "dc_sub None 2356"
  by (dc_eval dc_nc_2356)

lemma dc_nc_2357: "dc_sub None 2357"
  by (dc_eval dc_nc_2357)

lemma dc_nc_2358: "dc_sub None 2358"
  by (dc_eval dc_nc_2358)

lemma dc_nc_2359: "dc_sub None 2359"
  by (dc_eval dc_nc_2359)

lemma dc_nc_2360: "dc_sub None 2360"
  by (dc_eval dc_nc_2360)

lemma dc_nc_2361: "dc_sub None 2361"
  by (dc_eval dc_nc_2361)

lemma dc_nc_2362: "dc_sub None 2362"
  by (dc_eval dc_nc_2362)

lemma dc_nc_2363: "dc_sub None 2363"
  by (dc_eval dc_nc_2363)

lemma dc_nc_2364: "dc_sub None 2364"
  by (dc_eval dc_nc_2364)

lemma dc_nc_2365: "dc_sub None 2365"
  by (dc_eval dc_nc_2365)

lemma dc_nc_2366: "dc_sub None 2366"
  by (dc_eval dc_nc_2366)

lemma dc_nc_2367: "dc_sub None 2367"
  by (dc_eval dc_nc_2367)

lemma upt_nc_147: "[2352..<2368] = [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]"
  by (simp add: upt_rec)

lemma sec_nc_147: "\<forall>j\<in>{16 * 147..<16 * 147 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 147..<16 * 147 + 16}"
  then have "j \<in> set [2352..<2368]" unfolding set_upt by simp
  then have "j \<in> set [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]" unfolding upt_nc_147 .
  then show "dc_sub None j" using dc_nc_2352 dc_nc_2353 dc_nc_2354 dc_nc_2355 dc_nc_2356 dc_nc_2357 dc_nc_2358 dc_nc_2359 dc_nc_2360 dc_nc_2361 dc_nc_2362 dc_nc_2363 dc_nc_2364 dc_nc_2365 dc_nc_2366 dc_nc_2367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
