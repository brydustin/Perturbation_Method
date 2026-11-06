theory DCX_nc_154
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2464: "dc_sub None 2464"
  by (dc_eval dc_nc_2464)

lemma dc_nc_2465: "dc_sub None 2465"
  by (dc_eval dc_nc_2465)

lemma dc_nc_2466: "dc_sub None 2466"
  by (dc_eval dc_nc_2466)

lemma dc_nc_2467: "dc_sub None 2467"
  by (dc_eval dc_nc_2467)

lemma dc_nc_2468: "dc_sub None 2468"
  by (dc_eval dc_nc_2468)

lemma dc_nc_2469: "dc_sub None 2469"
  by (dc_eval dc_nc_2469)

lemma dc_nc_2470: "dc_sub None 2470"
  by (dc_eval dc_nc_2470)

lemma dc_nc_2471: "dc_sub None 2471"
  by (dc_eval dc_nc_2471)

lemma dc_nc_2472: "dc_sub None 2472"
  by (dc_eval dc_nc_2472)

lemma dc_nc_2473: "dc_sub None 2473"
  by (dc_eval dc_nc_2473)

lemma dc_nc_2474: "dc_sub None 2474"
  by (dc_eval dc_nc_2474)

lemma dc_nc_2475: "dc_sub None 2475"
  by (dc_eval dc_nc_2475)

lemma dc_nc_2476: "dc_sub None 2476"
  by (dc_eval dc_nc_2476)

lemma dc_nc_2477: "dc_sub None 2477"
  by (dc_eval dc_nc_2477)

lemma dc_nc_2478: "dc_sub None 2478"
  by (dc_eval dc_nc_2478)

lemma dc_nc_2479: "dc_sub None 2479"
  by (dc_eval dc_nc_2479)

lemma upt_nc_154: "[2464..<2480] = [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]"
  by (simp add: upt_rec)

lemma sec_nc_154: "\<forall>j\<in>{16 * 154..<16 * 154 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 154..<16 * 154 + 16}"
  then have "j \<in> set [2464..<2480]" unfolding set_upt by simp
  then have "j \<in> set [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]" unfolding upt_nc_154 .
  then show "dc_sub None j" using dc_nc_2464 dc_nc_2465 dc_nc_2466 dc_nc_2467 dc_nc_2468 dc_nc_2469 dc_nc_2470 dc_nc_2471 dc_nc_2472 dc_nc_2473 dc_nc_2474 dc_nc_2475 dc_nc_2476 dc_nc_2477 dc_nc_2478 dc_nc_2479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
