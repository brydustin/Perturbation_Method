theory GDCX_nc_142
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2272: "gdc_sub None 2272"
  by (gdc_eval gdc_nc_2272)

lemma gdc_nc_2273: "gdc_sub None 2273"
  by (gdc_eval gdc_nc_2273)

lemma gdc_nc_2274: "gdc_sub None 2274"
  by (gdc_eval gdc_nc_2274)

lemma gdc_nc_2275: "gdc_sub None 2275"
  by (gdc_eval gdc_nc_2275)

lemma gdc_nc_2276: "gdc_sub None 2276"
  by (gdc_eval gdc_nc_2276)

lemma gdc_nc_2277: "gdc_sub None 2277"
  by (gdc_eval gdc_nc_2277)

lemma gdc_nc_2278: "gdc_sub None 2278"
  by (gdc_eval gdc_nc_2278)

lemma gdc_nc_2279: "gdc_sub None 2279"
  by (gdc_eval gdc_nc_2279)

lemma gdc_nc_2280: "gdc_sub None 2280"
  by (gdc_eval gdc_nc_2280)

lemma gdc_nc_2281: "gdc_sub None 2281"
  by (gdc_eval gdc_nc_2281)

lemma gdc_nc_2282: "gdc_sub None 2282"
  by (gdc_eval gdc_nc_2282)

lemma gdc_nc_2283: "gdc_sub None 2283"
  by (gdc_eval gdc_nc_2283)

lemma gdc_nc_2284: "gdc_sub None 2284"
  by (gdc_eval gdc_nc_2284)

lemma gdc_nc_2285: "gdc_sub None 2285"
  by (gdc_eval gdc_nc_2285)

lemma gdc_nc_2286: "gdc_sub None 2286"
  by (gdc_eval gdc_nc_2286)

lemma gdc_nc_2287: "gdc_sub None 2287"
  by (gdc_eval gdc_nc_2287)

lemma gupt_nc_142: "[2272..<2288] = [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]"
  by (simp add: upt_rec)

lemma gsec_nc_142: "\<forall>j\<in>{16 * 142..<16 * 142 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 142..<16 * 142 + 16}"
  then have "j \<in> set [2272..<2288]" unfolding set_upt by simp
  then have "j \<in> set [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]" unfolding gupt_nc_142 .
  then show "gdc_sub None j" using gdc_nc_2272 gdc_nc_2273 gdc_nc_2274 gdc_nc_2275 gdc_nc_2276 gdc_nc_2277 gdc_nc_2278 gdc_nc_2279 gdc_nc_2280 gdc_nc_2281 gdc_nc_2282 gdc_nc_2283 gdc_nc_2284 gdc_nc_2285 gdc_nc_2286 gdc_nc_2287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
