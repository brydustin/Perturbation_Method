theory GOCX_nc_142
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2272: "goc_sub None 2272"
  by (goc_eval goc_nc_2272)

lemma goc_nc_2273: "goc_sub None 2273"
  by (goc_eval goc_nc_2273)

lemma goc_nc_2274: "goc_sub None 2274"
  by (goc_eval goc_nc_2274)

lemma goc_nc_2275: "goc_sub None 2275"
  by (goc_eval goc_nc_2275)

lemma goc_nc_2276: "goc_sub None 2276"
  by (goc_eval goc_nc_2276)

lemma goc_nc_2277: "goc_sub None 2277"
  by (goc_eval goc_nc_2277)

lemma goc_nc_2278: "goc_sub None 2278"
  by (goc_eval goc_nc_2278)

lemma goc_nc_2279: "goc_sub None 2279"
  by (goc_eval goc_nc_2279)

lemma goc_nc_2280: "goc_sub None 2280"
  by (goc_eval goc_nc_2280)

lemma goc_nc_2281: "goc_sub None 2281"
  by (goc_eval goc_nc_2281)

lemma goc_nc_2282: "goc_sub None 2282"
  by (goc_eval goc_nc_2282)

lemma goc_nc_2283: "goc_sub None 2283"
  by (goc_eval goc_nc_2283)

lemma goc_nc_2284: "goc_sub None 2284"
  by (goc_eval goc_nc_2284)

lemma goc_nc_2285: "goc_sub None 2285"
  by (goc_eval goc_nc_2285)

lemma goc_nc_2286: "goc_sub None 2286"
  by (goc_eval goc_nc_2286)

lemma goc_nc_2287: "goc_sub None 2287"
  by (goc_eval goc_nc_2287)

lemma gupt_nc_142: "[2272..<2288] = [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]"
  by (simp add: upt_rec)

lemma gsec_nc_142: "\<forall>j\<in>{16 * 142..<16 * 142 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 142..<16 * 142 + 16}"
  then have "j \<in> set [2272..<2288]" unfolding set_upt by simp
  then have "j \<in> set [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]" unfolding gupt_nc_142 .
  then show "goc_sub None j" using goc_nc_2272 goc_nc_2273 goc_nc_2274 goc_nc_2275 goc_nc_2276 goc_nc_2277 goc_nc_2278 goc_nc_2279 goc_nc_2280 goc_nc_2281 goc_nc_2282 goc_nc_2283 goc_nc_2284 goc_nc_2285 goc_nc_2286 goc_nc_2287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
