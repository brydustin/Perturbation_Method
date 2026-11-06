theory OCX_c30_142
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2272: "oc_sub oc_b30 2272"
  by (oc_eval oc_c30_2272)

lemma oc_c30_2273: "oc_sub oc_b30 2273"
  by (oc_eval oc_c30_2273)

lemma oc_c30_2274: "oc_sub oc_b30 2274"
  by (oc_eval oc_c30_2274)

lemma oc_c30_2275: "oc_sub oc_b30 2275"
  by (oc_eval oc_c30_2275)

lemma oc_c30_2276: "oc_sub oc_b30 2276"
  by (oc_eval oc_c30_2276)

lemma oc_c30_2277: "oc_sub oc_b30 2277"
  by (oc_eval oc_c30_2277)

lemma oc_c30_2278: "oc_sub oc_b30 2278"
  by (oc_eval oc_c30_2278)

lemma oc_c30_2279: "oc_sub oc_b30 2279"
  by (oc_eval oc_c30_2279)

lemma oc_c30_2280: "oc_sub oc_b30 2280"
  by (oc_eval oc_c30_2280)

lemma oc_c30_2281: "oc_sub oc_b30 2281"
  by (oc_eval oc_c30_2281)

lemma oc_c30_2282: "oc_sub oc_b30 2282"
  by (oc_eval oc_c30_2282)

lemma oc_c30_2283: "oc_sub oc_b30 2283"
  by (oc_eval oc_c30_2283)

lemma oc_c30_2284: "oc_sub oc_b30 2284"
  by (oc_eval oc_c30_2284)

lemma oc_c30_2285: "oc_sub oc_b30 2285"
  by (oc_eval oc_c30_2285)

lemma oc_c30_2286: "oc_sub oc_b30 2286"
  by (oc_eval oc_c30_2286)

lemma oc_c30_2287: "oc_sub oc_b30 2287"
  by (oc_eval oc_c30_2287)

lemma upt_c30_142: "[2272..<2288] = [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]"
  by (simp add: upt_rec)

lemma sec_c30_142: "\<forall>j\<in>{16 * 142..<16 * 142 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 142..<16 * 142 + 16}"
  then have "j \<in> set [2272..<2288]" unfolding set_upt by simp
  then have "j \<in> set [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]" unfolding upt_c30_142 .
  then show "oc_sub oc_b30 j" using oc_c30_2272 oc_c30_2273 oc_c30_2274 oc_c30_2275 oc_c30_2276 oc_c30_2277 oc_c30_2278 oc_c30_2279 oc_c30_2280 oc_c30_2281 oc_c30_2282 oc_c30_2283 oc_c30_2284 oc_c30_2285 oc_c30_2286 oc_c30_2287
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
