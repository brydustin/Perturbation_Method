theory GOCX_nc_149
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2384: "goc_sub None 2384"
  by (goc_eval goc_nc_2384)

lemma goc_nc_2385: "goc_sub None 2385"
  by (goc_eval goc_nc_2385)

lemma goc_nc_2386: "goc_sub None 2386"
  by (goc_eval goc_nc_2386)

lemma goc_nc_2387: "goc_sub None 2387"
  by (goc_eval goc_nc_2387)

lemma goc_nc_2388: "goc_sub None 2388"
  by (goc_eval goc_nc_2388)

lemma goc_nc_2389: "goc_sub None 2389"
  by (goc_eval goc_nc_2389)

lemma goc_nc_2390: "goc_sub None 2390"
  by (goc_eval goc_nc_2390)

lemma goc_nc_2391: "goc_sub None 2391"
  by (goc_eval goc_nc_2391)

lemma goc_nc_2392: "goc_sub None 2392"
  by (goc_eval goc_nc_2392)

lemma goc_nc_2393: "goc_sub None 2393"
  by (goc_eval goc_nc_2393)

lemma goc_nc_2394: "goc_sub None 2394"
  by (goc_eval goc_nc_2394)

lemma goc_nc_2395: "goc_sub None 2395"
  by (goc_eval goc_nc_2395)

lemma goc_nc_2396: "goc_sub None 2396"
  by (goc_eval goc_nc_2396)

lemma goc_nc_2397: "goc_sub None 2397"
  by (goc_eval goc_nc_2397)

lemma goc_nc_2398: "goc_sub None 2398"
  by (goc_eval goc_nc_2398)

lemma goc_nc_2399: "goc_sub None 2399"
  by (goc_eval goc_nc_2399)

lemma gupt_nc_149: "[2384..<2400] = [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]"
  by (simp add: upt_rec)

lemma gsec_nc_149: "\<forall>j\<in>{16 * 149..<16 * 149 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 149..<16 * 149 + 16}"
  then have "j \<in> set [2384..<2400]" unfolding set_upt by simp
  then have "j \<in> set [2384, 2385, 2386, 2387, 2388, 2389, 2390, 2391, 2392, 2393, 2394, 2395, 2396, 2397, 2398, 2399]" unfolding gupt_nc_149 .
  then show "goc_sub None j" using goc_nc_2384 goc_nc_2385 goc_nc_2386 goc_nc_2387 goc_nc_2388 goc_nc_2389 goc_nc_2390 goc_nc_2391 goc_nc_2392 goc_nc_2393 goc_nc_2394 goc_nc_2395 goc_nc_2396 goc_nc_2397 goc_nc_2398 goc_nc_2399
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
