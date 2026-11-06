theory OCX_c30_148
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2368: "oc_sub oc_b30 2368"
  by (oc_eval oc_c30_2368)

lemma oc_c30_2369: "oc_sub oc_b30 2369"
  by (oc_eval oc_c30_2369)

lemma oc_c30_2370: "oc_sub oc_b30 2370"
  by (oc_eval oc_c30_2370)

lemma oc_c30_2371: "oc_sub oc_b30 2371"
  by (oc_eval oc_c30_2371)

lemma oc_c30_2372: "oc_sub oc_b30 2372"
  by (oc_eval oc_c30_2372)

lemma oc_c30_2373: "oc_sub oc_b30 2373"
  by (oc_eval oc_c30_2373)

lemma oc_c30_2374: "oc_sub oc_b30 2374"
  by (oc_eval oc_c30_2374)

lemma oc_c30_2375: "oc_sub oc_b30 2375"
  by (oc_eval oc_c30_2375)

lemma oc_c30_2376: "oc_sub oc_b30 2376"
  by (oc_eval oc_c30_2376)

lemma oc_c30_2377: "oc_sub oc_b30 2377"
  by (oc_eval oc_c30_2377)

lemma oc_c30_2378: "oc_sub oc_b30 2378"
  by (oc_eval oc_c30_2378)

lemma oc_c30_2379: "oc_sub oc_b30 2379"
  by (oc_eval oc_c30_2379)

lemma oc_c30_2380: "oc_sub oc_b30 2380"
  by (oc_eval oc_c30_2380)

lemma oc_c30_2381: "oc_sub oc_b30 2381"
  by (oc_eval oc_c30_2381)

lemma oc_c30_2382: "oc_sub oc_b30 2382"
  by (oc_eval oc_c30_2382)

lemma oc_c30_2383: "oc_sub oc_b30 2383"
  by (oc_eval oc_c30_2383)

lemma upt_c30_148: "[2368..<2384] = [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]"
  by (simp add: upt_rec)

lemma sec_c30_148: "\<forall>j\<in>{16 * 148..<16 * 148 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 148..<16 * 148 + 16}"
  then have "j \<in> set [2368..<2384]" unfolding set_upt by simp
  then have "j \<in> set [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]" unfolding upt_c30_148 .
  then show "oc_sub oc_b30 j" using oc_c30_2368 oc_c30_2369 oc_c30_2370 oc_c30_2371 oc_c30_2372 oc_c30_2373 oc_c30_2374 oc_c30_2375 oc_c30_2376 oc_c30_2377 oc_c30_2378 oc_c30_2379 oc_c30_2380 oc_c30_2381 oc_c30_2382 oc_c30_2383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
