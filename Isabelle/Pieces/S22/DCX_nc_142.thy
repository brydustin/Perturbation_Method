theory DCX_nc_142
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2272: "dc_sub None 2272"
  by (dc_eval dc_nc_2272)

lemma dc_nc_2273: "dc_sub None 2273"
  by (dc_eval dc_nc_2273)

lemma dc_nc_2274: "dc_sub None 2274"
  by (dc_eval dc_nc_2274)

lemma dc_nc_2275: "dc_sub None 2275"
  by (dc_eval dc_nc_2275)

lemma dc_nc_2276: "dc_sub None 2276"
  by (dc_eval dc_nc_2276)

lemma dc_nc_2277: "dc_sub None 2277"
  by (dc_eval dc_nc_2277)

lemma dc_nc_2278: "dc_sub None 2278"
  by (dc_eval dc_nc_2278)

lemma dc_nc_2279: "dc_sub None 2279"
  by (dc_eval dc_nc_2279)

lemma dc_nc_2280: "dc_sub None 2280"
  by (dc_eval dc_nc_2280)

lemma dc_nc_2281: "dc_sub None 2281"
  by (dc_eval dc_nc_2281)

lemma dc_nc_2282: "dc_sub None 2282"
  by (dc_eval dc_nc_2282)

lemma dc_nc_2283: "dc_sub None 2283"
  by (dc_eval dc_nc_2283)

lemma dc_nc_2284: "dc_sub None 2284"
  by (dc_eval dc_nc_2284)

lemma dc_nc_2285: "dc_sub None 2285"
  by (dc_eval dc_nc_2285)

lemma dc_nc_2286: "dc_sub None 2286"
  by (dc_eval dc_nc_2286)

lemma dc_nc_2287: "dc_sub None 2287"
  by (dc_eval dc_nc_2287)

lemma upt_nc_142: "[2272..<2288] = [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]"
  by (simp add: upt_rec)

lemma sec_nc_142: "\<forall>j\<in>{16 * 142..<16 * 142 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 142..<16 * 142 + 16}"
  then have "j \<in> set [2272..<2288]" unfolding set_upt by simp
  then have "j \<in> set [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]" unfolding upt_nc_142 .
  then show "dc_sub None j" using dc_nc_2272 dc_nc_2273 dc_nc_2274 dc_nc_2275 dc_nc_2276 dc_nc_2277 dc_nc_2278 dc_nc_2279 dc_nc_2280 dc_nc_2281 dc_nc_2282 dc_nc_2283 dc_nc_2284 dc_nc_2285 dc_nc_2286 dc_nc_2287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
