theory OCX_c30_029
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0464: "oc_sub oc_b30 464"
  by (oc_eval oc_c30_0464)

lemma oc_c30_0465: "oc_sub oc_b30 465"
  by (oc_eval oc_c30_0465)

lemma oc_c30_0466: "oc_sub oc_b30 466"
  by (oc_eval oc_c30_0466)

lemma oc_c30_0467: "oc_sub oc_b30 467"
  by (oc_eval oc_c30_0467)

lemma oc_c30_0468: "oc_sub oc_b30 468"
  by (oc_eval oc_c30_0468)

lemma oc_c30_0469: "oc_sub oc_b30 469"
  by (oc_eval oc_c30_0469)

lemma oc_c30_0470: "oc_sub oc_b30 470"
  by (oc_eval oc_c30_0470)

lemma oc_c30_0471: "oc_sub oc_b30 471"
  by (oc_eval oc_c30_0471)

lemma oc_c30_0472: "oc_sub oc_b30 472"
  by (oc_eval oc_c30_0472)

lemma oc_c30_0473: "oc_sub oc_b30 473"
  by (oc_eval oc_c30_0473)

lemma oc_c30_0474: "oc_sub oc_b30 474"
  by (oc_eval oc_c30_0474)

lemma oc_c30_0475: "oc_sub oc_b30 475"
  by (oc_eval oc_c30_0475)

lemma oc_c30_0476: "oc_sub oc_b30 476"
  by (oc_eval oc_c30_0476)

lemma oc_c30_0477: "oc_sub oc_b30 477"
  by (oc_eval oc_c30_0477)

lemma oc_c30_0478: "oc_sub oc_b30 478"
  by (oc_eval oc_c30_0478)

lemma oc_c30_0479: "oc_sub oc_b30 479"
  by (oc_eval oc_c30_0479)

lemma upt_c30_029: "[464..<480] = [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]"
  by (simp add: upt_rec)

lemma sec_c30_029: "\<forall>j\<in>{16 * 29..<16 * 29 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 29..<16 * 29 + 16}"
  then have "j \<in> set [464..<480]" unfolding set_upt by simp
  then have "j \<in> set [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]" unfolding upt_c30_029 .
  then show "oc_sub oc_b30 j" using oc_c30_0464 oc_c30_0465 oc_c30_0466 oc_c30_0467 oc_c30_0468 oc_c30_0469 oc_c30_0470 oc_c30_0471 oc_c30_0472 oc_c30_0473 oc_c30_0474 oc_c30_0475 oc_c30_0476 oc_c30_0477 oc_c30_0478 oc_c30_0479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
