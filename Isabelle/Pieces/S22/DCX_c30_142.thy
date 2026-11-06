theory DCX_c30_142
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2272: "dc_sub dc_b30 2272"
  by (dc_eval dc_c30_2272)

lemma dc_c30_2273: "dc_sub dc_b30 2273"
  by (dc_eval dc_c30_2273)

lemma dc_c30_2274: "dc_sub dc_b30 2274"
  by (dc_eval dc_c30_2274)

lemma dc_c30_2275: "dc_sub dc_b30 2275"
  by (dc_eval dc_c30_2275)

lemma dc_c30_2276: "dc_sub dc_b30 2276"
  by (dc_eval dc_c30_2276)

lemma dc_c30_2277: "dc_sub dc_b30 2277"
  by (dc_eval dc_c30_2277)

lemma dc_c30_2278: "dc_sub dc_b30 2278"
  by (dc_eval dc_c30_2278)

lemma dc_c30_2279: "dc_sub dc_b30 2279"
  by (dc_eval dc_c30_2279)

lemma dc_c30_2280: "dc_sub dc_b30 2280"
  by (dc_eval dc_c30_2280)

lemma dc_c30_2281: "dc_sub dc_b30 2281"
  by (dc_eval dc_c30_2281)

lemma dc_c30_2282: "dc_sub dc_b30 2282"
  by (dc_eval dc_c30_2282)

lemma dc_c30_2283: "dc_sub dc_b30 2283"
  by (dc_eval dc_c30_2283)

lemma dc_c30_2284: "dc_sub dc_b30 2284"
  by (dc_eval dc_c30_2284)

lemma dc_c30_2285: "dc_sub dc_b30 2285"
  by (dc_eval dc_c30_2285)

lemma dc_c30_2286: "dc_sub dc_b30 2286"
  by (dc_eval dc_c30_2286)

lemma dc_c30_2287: "dc_sub dc_b30 2287"
  by (dc_eval dc_c30_2287)

lemma upt_c30_142: "[2272..<2288] = [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]"
  by (simp add: upt_rec)

lemma sec_c30_142: "\<forall>j\<in>{16 * 142..<16 * 142 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 142..<16 * 142 + 16}"
  then have "j \<in> set [2272..<2288]" unfolding set_upt by simp
  then have "j \<in> set [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]" unfolding upt_c30_142 .
  then show "dc_sub dc_b30 j" using dc_c30_2272 dc_c30_2273 dc_c30_2274 dc_c30_2275 dc_c30_2276 dc_c30_2277 dc_c30_2278 dc_c30_2279 dc_c30_2280 dc_c30_2281 dc_c30_2282 dc_c30_2283 dc_c30_2284 dc_c30_2285 dc_c30_2286 dc_c30_2287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
