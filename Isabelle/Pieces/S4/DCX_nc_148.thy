theory DCX_nc_148
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2368: "dc_sub None 2368"
  by (dc_eval dc_nc_2368)

lemma dc_nc_2369: "dc_sub None 2369"
  by (dc_eval dc_nc_2369)

lemma dc_nc_2370: "dc_sub None 2370"
  by (dc_eval dc_nc_2370)

lemma dc_nc_2371: "dc_sub None 2371"
  by (dc_eval dc_nc_2371)

lemma dc_nc_2372: "dc_sub None 2372"
  by (dc_eval dc_nc_2372)

lemma dc_nc_2373: "dc_sub None 2373"
  by (dc_eval dc_nc_2373)

lemma dc_nc_2374: "dc_sub None 2374"
  by (dc_eval dc_nc_2374)

lemma dc_nc_2375: "dc_sub None 2375"
  by (dc_eval dc_nc_2375)

lemma dc_nc_2376: "dc_sub None 2376"
  by (dc_eval dc_nc_2376)

lemma dc_nc_2377: "dc_sub None 2377"
  by (dc_eval dc_nc_2377)

lemma dc_nc_2378: "dc_sub None 2378"
  by (dc_eval dc_nc_2378)

lemma dc_nc_2379: "dc_sub None 2379"
  by (dc_eval dc_nc_2379)

lemma dc_nc_2380: "dc_sub None 2380"
  by (dc_eval dc_nc_2380)

lemma dc_nc_2381: "dc_sub None 2381"
  by (dc_eval dc_nc_2381)

lemma dc_nc_2382: "dc_sub None 2382"
  by (dc_eval dc_nc_2382)

lemma dc_nc_2383: "dc_sub None 2383"
  by (dc_eval dc_nc_2383)

lemma upt_nc_148: "[2368..<2384] = [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]"
  by (simp add: upt_rec)

lemma sec_nc_148: "\<forall>j\<in>{16 * 148..<16 * 148 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 148..<16 * 148 + 16}"
  then have "j \<in> set [2368..<2384]" unfolding set_upt by simp
  then have "j \<in> set [2368, 2369, 2370, 2371, 2372, 2373, 2374, 2375, 2376, 2377, 2378, 2379, 2380, 2381, 2382, 2383]" unfolding upt_nc_148 .
  then show "dc_sub None j" using dc_nc_2368 dc_nc_2369 dc_nc_2370 dc_nc_2371 dc_nc_2372 dc_nc_2373 dc_nc_2374 dc_nc_2375 dc_nc_2376 dc_nc_2377 dc_nc_2378 dc_nc_2379 dc_nc_2380 dc_nc_2381 dc_nc_2382 dc_nc_2383
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
