theory DCX_c30_154
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2464: "dc_sub dc_b30 2464"
  by (dc_eval dc_c30_2464)

lemma dc_c30_2465: "dc_sub dc_b30 2465"
  by (dc_eval dc_c30_2465)

lemma dc_c30_2466: "dc_sub dc_b30 2466"
  by (dc_eval dc_c30_2466)

lemma dc_c30_2467: "dc_sub dc_b30 2467"
  by (dc_eval dc_c30_2467)

lemma dc_c30_2468: "dc_sub dc_b30 2468"
  by (dc_eval dc_c30_2468)

lemma dc_c30_2469: "dc_sub dc_b30 2469"
  by (dc_eval dc_c30_2469)

lemma dc_c30_2470: "dc_sub dc_b30 2470"
  by (dc_eval dc_c30_2470)

lemma dc_c30_2471: "dc_sub dc_b30 2471"
  by (dc_eval dc_c30_2471)

lemma dc_c30_2472: "dc_sub dc_b30 2472"
  by (dc_eval dc_c30_2472)

lemma dc_c30_2473: "dc_sub dc_b30 2473"
  by (dc_eval dc_c30_2473)

lemma dc_c30_2474: "dc_sub dc_b30 2474"
  by (dc_eval dc_c30_2474)

lemma dc_c30_2475: "dc_sub dc_b30 2475"
  by (dc_eval dc_c30_2475)

lemma dc_c30_2476: "dc_sub dc_b30 2476"
  by (dc_eval dc_c30_2476)

lemma dc_c30_2477: "dc_sub dc_b30 2477"
  by (dc_eval dc_c30_2477)

lemma dc_c30_2478: "dc_sub dc_b30 2478"
  by (dc_eval dc_c30_2478)

lemma dc_c30_2479: "dc_sub dc_b30 2479"
  by (dc_eval dc_c30_2479)

lemma upt_c30_154: "[2464..<2480] = [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]"
  by (simp add: upt_rec)

lemma sec_c30_154: "\<forall>j\<in>{16 * 154..<16 * 154 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 154..<16 * 154 + 16}"
  then have "j \<in> set [2464..<2480]" unfolding set_upt by simp
  then have "j \<in> set [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]" unfolding upt_c30_154 .
  then show "dc_sub dc_b30 j" using dc_c30_2464 dc_c30_2465 dc_c30_2466 dc_c30_2467 dc_c30_2468 dc_c30_2469 dc_c30_2470 dc_c30_2471 dc_c30_2472 dc_c30_2473 dc_c30_2474 dc_c30_2475 dc_c30_2476 dc_c30_2477 dc_c30_2478 dc_c30_2479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
