theory GDCX_nc_149
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2384: "gdc_sub None 2384"
  by (gdc_eval gdc_nc_2384)

lemma gdc_nc_2385: "gdc_sub None 2385"
  by (gdc_eval gdc_nc_2385)

lemma gdc_nc_2386: "gdc_sub None 2386"
  by (gdc_eval gdc_nc_2386)

lemma gdc_nc_2387: "gdc_sub None 2387"
  by (gdc_eval gdc_nc_2387)

lemma gdc_nc_2388: "gdc_sub None 2388"
  by (gdc_eval gdc_nc_2388)

lemma gdc_nc_2389: "gdc_sub None 2389"
  by (gdc_eval gdc_nc_2389)

lemma gdc_nc_2390: "gdc_sub None 2390"
  by (gdc_eval gdc_nc_2390)

lemma gdc_nc_2391: "gdc_sub None 2391"
  by (gdc_eval gdc_nc_2391)

lemma gdc_nc_2392: "gdc_sub None 2392"
  by (gdc_eval gdc_nc_2392)

lemma gdc_nc_2393: "gdc_sub None 2393"
  by (gdc_eval gdc_nc_2393)

lemma gdc_nc_2394: "gdc_sub None 2394"
  by (gdc_eval gdc_nc_2394)

lemma gdc_nc_2395: "gdc_sub None 2395"
  by (gdc_eval gdc_nc_2395)

lemma gdc_nc_2396: "gdc_sub None 2396"
  by (gdc_eval gdc_nc_2396)

lemma gdc_nc_2397: "gdc_sub None 2397"
  by (gdc_eval gdc_nc_2397)

lemma gdc_nc_2398: "gdc_sub None 2398"
  by (gdc_eval gdc_nc_2398)

lemma gdc_nc_2399: "gdc_sub None 2399"
  by (gdc_eval gdc_nc_2399)

lemma gupt_nc_149: "[2384..<2400] = [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]"
  by (simp add: upt_rec)

lemma gsec_nc_149: "\<forall>j\<in>{16 * 149..<16 * 149 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 149..<16 * 149 + 16}"
  then have "j \<in> set [2384..<2400]" unfolding set_upt by simp
  then have "j \<in> set [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]" unfolding gupt_nc_149 .
  then show "gdc_sub None j" using gdc_nc_2384 gdc_nc_2385 gdc_nc_2386 gdc_nc_2387 gdc_nc_2388 gdc_nc_2389 gdc_nc_2390 gdc_nc_2391 gdc_nc_2392 gdc_nc_2393 gdc_nc_2394 gdc_nc_2395 gdc_nc_2396 gdc_nc_2397 gdc_nc_2398 gdc_nc_2399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
