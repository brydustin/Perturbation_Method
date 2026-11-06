theory GOCX_nc_148
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2368: "goc_sub None 2368"
  by (goc_eval goc_nc_2368)

lemma goc_nc_2369: "goc_sub None 2369"
  by (goc_eval goc_nc_2369)

lemma goc_nc_2370: "goc_sub None 2370"
  by (goc_eval goc_nc_2370)

lemma goc_nc_2371: "goc_sub None 2371"
  by (goc_eval goc_nc_2371)

lemma goc_nc_2372: "goc_sub None 2372"
  by (goc_eval goc_nc_2372)

lemma goc_nc_2373: "goc_sub None 2373"
  by (goc_eval goc_nc_2373)

lemma goc_nc_2374: "goc_sub None 2374"
  by (goc_eval goc_nc_2374)

lemma goc_nc_2375: "goc_sub None 2375"
  by (goc_eval goc_nc_2375)

lemma goc_nc_2376: "goc_sub None 2376"
  by (goc_eval goc_nc_2376)

lemma goc_nc_2377: "goc_sub None 2377"
  by (goc_eval goc_nc_2377)

lemma goc_nc_2378: "goc_sub None 2378"
  by (goc_eval goc_nc_2378)

lemma goc_nc_2379: "goc_sub None 2379"
  by (goc_eval goc_nc_2379)

lemma goc_nc_2380: "goc_sub None 2380"
  by (goc_eval goc_nc_2380)

lemma goc_nc_2381: "goc_sub None 2381"
  by (goc_eval goc_nc_2381)

lemma goc_nc_2382: "goc_sub None 2382"
  by (goc_eval goc_nc_2382)

lemma goc_nc_2383: "goc_sub None 2383"
  by (goc_eval goc_nc_2383)

lemma gupt_nc_148: "[2368..<2384] = [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]"
  by (simp add: upt_rec)

lemma gsec_nc_148: "\<forall>j\<in>{16 * 148..<16 * 148 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 148..<16 * 148 + 16}"
  then have "j \<in> set [2368..<2384]" unfolding set_upt by simp
  then have "j \<in> set [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]" unfolding gupt_nc_148 .
  then show "goc_sub None j" using goc_nc_2368 goc_nc_2369 goc_nc_2370 goc_nc_2371 goc_nc_2372 goc_nc_2373 goc_nc_2374 goc_nc_2375 goc_nc_2376 goc_nc_2377 goc_nc_2378 goc_nc_2379 goc_nc_2380 goc_nc_2381 goc_nc_2382 goc_nc_2383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
