theory OCX_c30_154
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2464: "oc_sub oc_b30 2464"
  by (oc_eval oc_c30_2464)

lemma oc_c30_2465: "oc_sub oc_b30 2465"
  by (oc_eval oc_c30_2465)

lemma oc_c30_2466: "oc_sub oc_b30 2466"
  by (oc_eval oc_c30_2466)

lemma oc_c30_2467: "oc_sub oc_b30 2467"
  by (oc_eval oc_c30_2467)

lemma oc_c30_2468: "oc_sub oc_b30 2468"
  by (oc_eval oc_c30_2468)

lemma oc_c30_2469: "oc_sub oc_b30 2469"
  by (oc_eval oc_c30_2469)

lemma oc_c30_2470: "oc_sub oc_b30 2470"
  by (oc_eval oc_c30_2470)

lemma oc_c30_2471: "oc_sub oc_b30 2471"
  by (oc_eval oc_c30_2471)

lemma oc_c30_2472: "oc_sub oc_b30 2472"
  by (oc_eval oc_c30_2472)

lemma oc_c30_2473: "oc_sub oc_b30 2473"
  by (oc_eval oc_c30_2473)

lemma oc_c30_2474: "oc_sub oc_b30 2474"
  by (oc_eval oc_c30_2474)

lemma oc_c30_2475: "oc_sub oc_b30 2475"
  by (oc_eval oc_c30_2475)

lemma oc_c30_2476: "oc_sub oc_b30 2476"
  by (oc_eval oc_c30_2476)

lemma oc_c30_2477: "oc_sub oc_b30 2477"
  by (oc_eval oc_c30_2477)

lemma oc_c30_2478: "oc_sub oc_b30 2478"
  by (oc_eval oc_c30_2478)

lemma oc_c30_2479: "oc_sub oc_b30 2479"
  by (oc_eval oc_c30_2479)

lemma upt_c30_154: "[2464..<2480] = [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]"
  by (simp add: upt_rec)

lemma sec_c30_154: "\<forall>j\<in>{16 * 154..<16 * 154 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 154..<16 * 154 + 16}"
  then have "j \<in> set [2464..<2480]" unfolding set_upt by simp
  then have "j \<in> set [2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479]" unfolding upt_c30_154 .
  then show "oc_sub oc_b30 j" using oc_c30_2464 oc_c30_2465 oc_c30_2466 oc_c30_2467 oc_c30_2468 oc_c30_2469 oc_c30_2470 oc_c30_2471 oc_c30_2472 oc_c30_2473 oc_c30_2474 oc_c30_2475 oc_c30_2476 oc_c30_2477 oc_c30_2478 oc_c30_2479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
