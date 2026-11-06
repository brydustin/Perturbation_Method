theory GDCX_nc_147
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2352: "gdc_sub None 2352"
  by (gdc_eval gdc_nc_2352)

lemma gdc_nc_2353: "gdc_sub None 2353"
  by (gdc_eval gdc_nc_2353)

lemma gdc_nc_2354: "gdc_sub None 2354"
  by (gdc_eval gdc_nc_2354)

lemma gdc_nc_2355: "gdc_sub None 2355"
  by (gdc_eval gdc_nc_2355)

lemma gdc_nc_2356: "gdc_sub None 2356"
  by (gdc_eval gdc_nc_2356)

lemma gdc_nc_2357: "gdc_sub None 2357"
  by (gdc_eval gdc_nc_2357)

lemma gdc_nc_2358: "gdc_sub None 2358"
  by (gdc_eval gdc_nc_2358)

lemma gdc_nc_2359: "gdc_sub None 2359"
  by (gdc_eval gdc_nc_2359)

lemma gdc_nc_2360: "gdc_sub None 2360"
  by (gdc_eval gdc_nc_2360)

lemma gdc_nc_2361: "gdc_sub None 2361"
  by (gdc_eval gdc_nc_2361)

lemma gdc_nc_2362: "gdc_sub None 2362"
  by (gdc_eval gdc_nc_2362)

lemma gdc_nc_2363: "gdc_sub None 2363"
  by (gdc_eval gdc_nc_2363)

lemma gdc_nc_2364: "gdc_sub None 2364"
  by (gdc_eval gdc_nc_2364)

lemma gdc_nc_2365: "gdc_sub None 2365"
  by (gdc_eval gdc_nc_2365)

lemma gdc_nc_2366: "gdc_sub None 2366"
  by (gdc_eval gdc_nc_2366)

lemma gdc_nc_2367: "gdc_sub None 2367"
  by (gdc_eval gdc_nc_2367)

lemma gupt_nc_147: "[2352..<2368] = [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]"
  by (simp add: upt_rec)

lemma gsec_nc_147: "\<forall>j\<in>{16 * 147..<16 * 147 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 147..<16 * 147 + 16}"
  then have "j \<in> set [2352..<2368]" unfolding set_upt by simp
  then have "j \<in> set [2352, 2353, 2354, 2355, 2356, 2357, 2358, 2359, 2360, 2361, 2362, 2363, 2364, 2365, 2366, 2367]" unfolding gupt_nc_147 .
  then show "gdc_sub None j" using gdc_nc_2352 gdc_nc_2353 gdc_nc_2354 gdc_nc_2355 gdc_nc_2356 gdc_nc_2357 gdc_nc_2358 gdc_nc_2359 gdc_nc_2360 gdc_nc_2361 gdc_nc_2362 gdc_nc_2363 gdc_nc_2364 gdc_nc_2365 gdc_nc_2366 gdc_nc_2367
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
