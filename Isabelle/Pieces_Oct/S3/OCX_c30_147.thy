theory OCX_c30_147
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2352: "oc_sub oc_b30 2352"
  by (oc_eval oc_c30_2352)

lemma oc_c30_2353: "oc_sub oc_b30 2353"
  by (oc_eval oc_c30_2353)

lemma oc_c30_2354: "oc_sub oc_b30 2354"
  by (oc_eval oc_c30_2354)

lemma oc_c30_2355: "oc_sub oc_b30 2355"
  by (oc_eval oc_c30_2355)

lemma oc_c30_2356: "oc_sub oc_b30 2356"
  by (oc_eval oc_c30_2356)

lemma oc_c30_2357: "oc_sub oc_b30 2357"
  by (oc_eval oc_c30_2357)

lemma oc_c30_2358: "oc_sub oc_b30 2358"
  by (oc_eval oc_c30_2358)

lemma oc_c30_2359: "oc_sub oc_b30 2359"
  by (oc_eval oc_c30_2359)

lemma oc_c30_2360: "oc_sub oc_b30 2360"
  by (oc_eval oc_c30_2360)

lemma oc_c30_2361: "oc_sub oc_b30 2361"
  by (oc_eval oc_c30_2361)

lemma oc_c30_2362: "oc_sub oc_b30 2362"
  by (oc_eval oc_c30_2362)

lemma oc_c30_2363: "oc_sub oc_b30 2363"
  by (oc_eval oc_c30_2363)

lemma oc_c30_2364: "oc_sub oc_b30 2364"
  by (oc_eval oc_c30_2364)

lemma oc_c30_2365: "oc_sub oc_b30 2365"
  by (oc_eval oc_c30_2365)

lemma oc_c30_2366: "oc_sub oc_b30 2366"
  by (oc_eval oc_c30_2366)

lemma oc_c30_2367: "oc_sub oc_b30 2367"
  by (oc_eval oc_c30_2367)

lemma upt_c30_147: "[2352..<2368] = [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]"
  by (simp add: upt_rec)

lemma sec_c30_147: "\<forall>j\<in>{16 * 147..<16 * 147 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 147..<16 * 147 + 16}"
  then have "j \<in> set [2352..<2368]" unfolding set_upt by simp
  then have "j \<in> set [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]" unfolding upt_c30_147 .
  then show "oc_sub oc_b30 j" using oc_c30_2352 oc_c30_2353 oc_c30_2354 oc_c30_2355 oc_c30_2356 oc_c30_2357 oc_c30_2358 oc_c30_2359 oc_c30_2360 oc_c30_2361 oc_c30_2362 oc_c30_2363 oc_c30_2364 oc_c30_2365 oc_c30_2366 oc_c30_2367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
