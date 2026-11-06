theory OCX_nc_148
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2368: "oc_sub None 2368"
  by (oc_eval oc_nc_2368)

lemma oc_nc_2369: "oc_sub None 2369"
  by (oc_eval oc_nc_2369)

lemma oc_nc_2370: "oc_sub None 2370"
  by (oc_eval oc_nc_2370)

lemma oc_nc_2371: "oc_sub None 2371"
  by (oc_eval oc_nc_2371)

lemma oc_nc_2372: "oc_sub None 2372"
  by (oc_eval oc_nc_2372)

lemma oc_nc_2373: "oc_sub None 2373"
  by (oc_eval oc_nc_2373)

lemma oc_nc_2374: "oc_sub None 2374"
  by (oc_eval oc_nc_2374)

lemma oc_nc_2375: "oc_sub None 2375"
  by (oc_eval oc_nc_2375)

lemma oc_nc_2376: "oc_sub None 2376"
  by (oc_eval oc_nc_2376)

lemma oc_nc_2377: "oc_sub None 2377"
  by (oc_eval oc_nc_2377)

lemma oc_nc_2378: "oc_sub None 2378"
  by (oc_eval oc_nc_2378)

lemma oc_nc_2379: "oc_sub None 2379"
  by (oc_eval oc_nc_2379)

lemma oc_nc_2380: "oc_sub None 2380"
  by (oc_eval oc_nc_2380)

lemma oc_nc_2381: "oc_sub None 2381"
  by (oc_eval oc_nc_2381)

lemma oc_nc_2382: "oc_sub None 2382"
  by (oc_eval oc_nc_2382)

lemma oc_nc_2383: "oc_sub None 2383"
  by (oc_eval oc_nc_2383)

lemma upt_nc_148: "[2368..<2384] = [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]"
  by (simp add: upt_rec)

lemma sec_nc_148: "\<forall>j\<in>{16 * 148..<16 * 148 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 148..<16 * 148 + 16}"
  then have "j \<in> set [2368..<2384]" unfolding set_upt by simp
  then have "j \<in> set [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]" unfolding upt_nc_148 .
  then show "oc_sub None j" using oc_nc_2368 oc_nc_2369 oc_nc_2370 oc_nc_2371 oc_nc_2372 oc_nc_2373 oc_nc_2374 oc_nc_2375 oc_nc_2376 oc_nc_2377 oc_nc_2378 oc_nc_2379 oc_nc_2380 oc_nc_2381 oc_nc_2382 oc_nc_2383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
