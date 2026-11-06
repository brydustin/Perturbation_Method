theory GDCX_nc_148
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2368: "gdc_sub None 2368"
  by (gdc_eval gdc_nc_2368)

lemma gdc_nc_2369: "gdc_sub None 2369"
  by (gdc_eval gdc_nc_2369)

lemma gdc_nc_2370: "gdc_sub None 2370"
  by (gdc_eval gdc_nc_2370)

lemma gdc_nc_2371: "gdc_sub None 2371"
  by (gdc_eval gdc_nc_2371)

lemma gdc_nc_2372: "gdc_sub None 2372"
  by (gdc_eval gdc_nc_2372)

lemma gdc_nc_2373: "gdc_sub None 2373"
  by (gdc_eval gdc_nc_2373)

lemma gdc_nc_2374: "gdc_sub None 2374"
  by (gdc_eval gdc_nc_2374)

lemma gdc_nc_2375: "gdc_sub None 2375"
  by (gdc_eval gdc_nc_2375)

lemma gdc_nc_2376: "gdc_sub None 2376"
  by (gdc_eval gdc_nc_2376)

lemma gdc_nc_2377: "gdc_sub None 2377"
  by (gdc_eval gdc_nc_2377)

lemma gdc_nc_2378: "gdc_sub None 2378"
  by (gdc_eval gdc_nc_2378)

lemma gdc_nc_2379: "gdc_sub None 2379"
  by (gdc_eval gdc_nc_2379)

lemma gdc_nc_2380: "gdc_sub None 2380"
  by (gdc_eval gdc_nc_2380)

lemma gdc_nc_2381: "gdc_sub None 2381"
  by (gdc_eval gdc_nc_2381)

lemma gdc_nc_2382: "gdc_sub None 2382"
  by (gdc_eval gdc_nc_2382)

lemma gdc_nc_2383: "gdc_sub None 2383"
  by (gdc_eval gdc_nc_2383)

lemma gupt_nc_148: "[2368..<2384] = [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]"
  by (simp add: upt_rec)

lemma gsec_nc_148: "\<forall>j\<in>{16 * 148..<16 * 148 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 148..<16 * 148 + 16}"
  then have "j \<in> set [2368..<2384]" unfolding set_upt by simp
  then have "j \<in> set [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]" unfolding gupt_nc_148 .
  then show "gdc_sub None j" using gdc_nc_2368 gdc_nc_2369 gdc_nc_2370 gdc_nc_2371 gdc_nc_2372 gdc_nc_2373 gdc_nc_2374 gdc_nc_2375 gdc_nc_2376 gdc_nc_2377 gdc_nc_2378 gdc_nc_2379 gdc_nc_2380 gdc_nc_2381 gdc_nc_2382 gdc_nc_2383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
