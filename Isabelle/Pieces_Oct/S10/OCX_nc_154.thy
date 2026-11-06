theory OCX_nc_154
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2464: "oc_sub None 2464"
  by (oc_eval oc_nc_2464)

lemma oc_nc_2465: "oc_sub None 2465"
  by (oc_eval oc_nc_2465)

lemma oc_nc_2466: "oc_sub None 2466"
  by (oc_eval oc_nc_2466)

lemma oc_nc_2467: "oc_sub None 2467"
  by (oc_eval oc_nc_2467)

lemma oc_nc_2468: "oc_sub None 2468"
  by (oc_eval oc_nc_2468)

lemma oc_nc_2469: "oc_sub None 2469"
  by (oc_eval oc_nc_2469)

lemma oc_nc_2470: "oc_sub None 2470"
  by (oc_eval oc_nc_2470)

lemma oc_nc_2471: "oc_sub None 2471"
  by (oc_eval oc_nc_2471)

lemma oc_nc_2472: "oc_sub None 2472"
  by (oc_eval oc_nc_2472)

lemma oc_nc_2473: "oc_sub None 2473"
  by (oc_eval oc_nc_2473)

lemma oc_nc_2474: "oc_sub None 2474"
  by (oc_eval oc_nc_2474)

lemma oc_nc_2475: "oc_sub None 2475"
  by (oc_eval oc_nc_2475)

lemma oc_nc_2476: "oc_sub None 2476"
  by (oc_eval oc_nc_2476)

lemma oc_nc_2477: "oc_sub None 2477"
  by (oc_eval oc_nc_2477)

lemma oc_nc_2478: "oc_sub None 2478"
  by (oc_eval oc_nc_2478)

lemma oc_nc_2479: "oc_sub None 2479"
  by (oc_eval oc_nc_2479)

lemma upt_nc_154: "[2464..<2480] = [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]"
  by (simp add: upt_rec)

lemma sec_nc_154: "\<forall>j\<in>{16 * 154..<16 * 154 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 154..<16 * 154 + 16}"
  then have "j \<in> set [2464..<2480]" unfolding set_upt by simp
  then have "j \<in> set [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]" unfolding upt_nc_154 .
  then show "oc_sub None j" using oc_nc_2464 oc_nc_2465 oc_nc_2466 oc_nc_2467 oc_nc_2468 oc_nc_2469 oc_nc_2470 oc_nc_2471 oc_nc_2472 oc_nc_2473 oc_nc_2474 oc_nc_2475 oc_nc_2476 oc_nc_2477 oc_nc_2478 oc_nc_2479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
