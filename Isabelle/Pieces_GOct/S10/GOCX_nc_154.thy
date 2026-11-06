theory GOCX_nc_154
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2464: "goc_sub None 2464"
  by (goc_eval goc_nc_2464)

lemma goc_nc_2465: "goc_sub None 2465"
  by (goc_eval goc_nc_2465)

lemma goc_nc_2466: "goc_sub None 2466"
  by (goc_eval goc_nc_2466)

lemma goc_nc_2467: "goc_sub None 2467"
  by (goc_eval goc_nc_2467)

lemma goc_nc_2468: "goc_sub None 2468"
  by (goc_eval goc_nc_2468)

lemma goc_nc_2469: "goc_sub None 2469"
  by (goc_eval goc_nc_2469)

lemma goc_nc_2470: "goc_sub None 2470"
  by (goc_eval goc_nc_2470)

lemma goc_nc_2471: "goc_sub None 2471"
  by (goc_eval goc_nc_2471)

lemma goc_nc_2472: "goc_sub None 2472"
  by (goc_eval goc_nc_2472)

lemma goc_nc_2473: "goc_sub None 2473"
  by (goc_eval goc_nc_2473)

lemma goc_nc_2474: "goc_sub None 2474"
  by (goc_eval goc_nc_2474)

lemma goc_nc_2475: "goc_sub None 2475"
  by (goc_eval goc_nc_2475)

lemma goc_nc_2476: "goc_sub None 2476"
  by (goc_eval goc_nc_2476)

lemma goc_nc_2477: "goc_sub None 2477"
  by (goc_eval goc_nc_2477)

lemma goc_nc_2478: "goc_sub None 2478"
  by (goc_eval goc_nc_2478)

lemma goc_nc_2479: "goc_sub None 2479"
  by (goc_eval goc_nc_2479)

lemma gupt_nc_154: "[2464..<2480] = [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]"
  by (simp add: upt_rec)

lemma gsec_nc_154: "\<forall>j\<in>{16 * 154..<16 * 154 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 154..<16 * 154 + 16}"
  then have "j \<in> set [2464..<2480]" unfolding set_upt by simp
  then have "j \<in> set [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]" unfolding gupt_nc_154 .
  then show "goc_sub None j" using goc_nc_2464 goc_nc_2465 goc_nc_2466 goc_nc_2467 goc_nc_2468 goc_nc_2469 goc_nc_2470 goc_nc_2471 goc_nc_2472 goc_nc_2473 goc_nc_2474 goc_nc_2475 goc_nc_2476 goc_nc_2477 goc_nc_2478 goc_nc_2479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
