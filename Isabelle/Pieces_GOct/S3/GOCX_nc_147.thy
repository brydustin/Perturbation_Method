theory GOCX_nc_147
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2352: "goc_sub None 2352"
  by (goc_eval goc_nc_2352)

lemma goc_nc_2353: "goc_sub None 2353"
  by (goc_eval goc_nc_2353)

lemma goc_nc_2354: "goc_sub None 2354"
  by (goc_eval goc_nc_2354)

lemma goc_nc_2355: "goc_sub None 2355"
  by (goc_eval goc_nc_2355)

lemma goc_nc_2356: "goc_sub None 2356"
  by (goc_eval goc_nc_2356)

lemma goc_nc_2357: "goc_sub None 2357"
  by (goc_eval goc_nc_2357)

lemma goc_nc_2358: "goc_sub None 2358"
  by (goc_eval goc_nc_2358)

lemma goc_nc_2359: "goc_sub None 2359"
  by (goc_eval goc_nc_2359)

lemma goc_nc_2360: "goc_sub None 2360"
  by (goc_eval goc_nc_2360)

lemma goc_nc_2361: "goc_sub None 2361"
  by (goc_eval goc_nc_2361)

lemma goc_nc_2362: "goc_sub None 2362"
  by (goc_eval goc_nc_2362)

lemma goc_nc_2363: "goc_sub None 2363"
  by (goc_eval goc_nc_2363)

lemma goc_nc_2364: "goc_sub None 2364"
  by (goc_eval goc_nc_2364)

lemma goc_nc_2365: "goc_sub None 2365"
  by (goc_eval goc_nc_2365)

lemma goc_nc_2366: "goc_sub None 2366"
  by (goc_eval goc_nc_2366)

lemma goc_nc_2367: "goc_sub None 2367"
  by (goc_eval goc_nc_2367)

lemma gupt_nc_147: "[2352..<2368] = [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]"
  by (simp add: upt_rec)

lemma gsec_nc_147: "\<forall>j\<in>{16 * 147..<16 * 147 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 147..<16 * 147 + 16}"
  then have "j \<in> set [2352..<2368]" unfolding set_upt by simp
  then have "j \<in> set [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]" unfolding gupt_nc_147 .
  then show "goc_sub None j" using goc_nc_2352 goc_nc_2353 goc_nc_2354 goc_nc_2355 goc_nc_2356 goc_nc_2357 goc_nc_2358 goc_nc_2359 goc_nc_2360 goc_nc_2361 goc_nc_2362 goc_nc_2363 goc_nc_2364 goc_nc_2365 goc_nc_2366 goc_nc_2367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
