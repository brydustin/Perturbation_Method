theory OCX_nc_147
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2352: "oc_sub None 2352"
  by (oc_eval oc_nc_2352)

lemma oc_nc_2353: "oc_sub None 2353"
  by (oc_eval oc_nc_2353)

lemma oc_nc_2354: "oc_sub None 2354"
  by (oc_eval oc_nc_2354)

lemma oc_nc_2355: "oc_sub None 2355"
  by (oc_eval oc_nc_2355)

lemma oc_nc_2356: "oc_sub None 2356"
  by (oc_eval oc_nc_2356)

lemma oc_nc_2357: "oc_sub None 2357"
  by (oc_eval oc_nc_2357)

lemma oc_nc_2358: "oc_sub None 2358"
  by (oc_eval oc_nc_2358)

lemma oc_nc_2359: "oc_sub None 2359"
  by (oc_eval oc_nc_2359)

lemma oc_nc_2360: "oc_sub None 2360"
  by (oc_eval oc_nc_2360)

lemma oc_nc_2361: "oc_sub None 2361"
  by (oc_eval oc_nc_2361)

lemma oc_nc_2362: "oc_sub None 2362"
  by (oc_eval oc_nc_2362)

lemma oc_nc_2363: "oc_sub None 2363"
  by (oc_eval oc_nc_2363)

lemma oc_nc_2364: "oc_sub None 2364"
  by (oc_eval oc_nc_2364)

lemma oc_nc_2365: "oc_sub None 2365"
  by (oc_eval oc_nc_2365)

lemma oc_nc_2366: "oc_sub None 2366"
  by (oc_eval oc_nc_2366)

lemma oc_nc_2367: "oc_sub None 2367"
  by (oc_eval oc_nc_2367)

lemma upt_nc_147: "[2352..<2368] = [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]"
  by (simp add: upt_rec)

lemma sec_nc_147: "\<forall>j\<in>{16 * 147..<16 * 147 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 147..<16 * 147 + 16}"
  then have "j \<in> set [2352..<2368]" unfolding set_upt by simp
  then have "j \<in> set [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]" unfolding upt_nc_147 .
  then show "oc_sub None j" using oc_nc_2352 oc_nc_2353 oc_nc_2354 oc_nc_2355 oc_nc_2356 oc_nc_2357 oc_nc_2358 oc_nc_2359 oc_nc_2360 oc_nc_2361 oc_nc_2362 oc_nc_2363 oc_nc_2364 oc_nc_2365 oc_nc_2366 oc_nc_2367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
