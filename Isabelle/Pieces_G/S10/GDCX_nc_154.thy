theory GDCX_nc_154
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2464: "gdc_sub None 2464"
  by (gdc_eval gdc_nc_2464)

lemma gdc_nc_2465: "gdc_sub None 2465"
  by (gdc_eval gdc_nc_2465)

lemma gdc_nc_2466: "gdc_sub None 2466"
  by (gdc_eval gdc_nc_2466)

lemma gdc_nc_2467: "gdc_sub None 2467"
  by (gdc_eval gdc_nc_2467)

lemma gdc_nc_2468: "gdc_sub None 2468"
  by (gdc_eval gdc_nc_2468)

lemma gdc_nc_2469: "gdc_sub None 2469"
  by (gdc_eval gdc_nc_2469)

lemma gdc_nc_2470: "gdc_sub None 2470"
  by (gdc_eval gdc_nc_2470)

lemma gdc_nc_2471: "gdc_sub None 2471"
  by (gdc_eval gdc_nc_2471)

lemma gdc_nc_2472: "gdc_sub None 2472"
  by (gdc_eval gdc_nc_2472)

lemma gdc_nc_2473: "gdc_sub None 2473"
  by (gdc_eval gdc_nc_2473)

lemma gdc_nc_2474: "gdc_sub None 2474"
  by (gdc_eval gdc_nc_2474)

lemma gdc_nc_2475: "gdc_sub None 2475"
  by (gdc_eval gdc_nc_2475)

lemma gdc_nc_2476: "gdc_sub None 2476"
  by (gdc_eval gdc_nc_2476)

lemma gdc_nc_2477: "gdc_sub None 2477"
  by (gdc_eval gdc_nc_2477)

lemma gdc_nc_2478: "gdc_sub None 2478"
  by (gdc_eval gdc_nc_2478)

lemma gdc_nc_2479: "gdc_sub None 2479"
  by (gdc_eval gdc_nc_2479)

lemma gupt_nc_154: "[2464..<2480] = [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]"
  by (simp add: upt_rec)

lemma gsec_nc_154: "\<forall>j\<in>{16 * 154..<16 * 154 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 154..<16 * 154 + 16}"
  then have "j \<in> set [2464..<2480]" unfolding set_upt by simp
  then have "j \<in> set [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]" unfolding gupt_nc_154 .
  then show "gdc_sub None j" using gdc_nc_2464 gdc_nc_2465 gdc_nc_2466 gdc_nc_2467 gdc_nc_2468 gdc_nc_2469 gdc_nc_2470 gdc_nc_2471 gdc_nc_2472 gdc_nc_2473 gdc_nc_2474 gdc_nc_2475 gdc_nc_2476 gdc_nc_2477 gdc_nc_2478 gdc_nc_2479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
