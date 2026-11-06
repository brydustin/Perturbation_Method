theory DCX_c30_029
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0464: "dc_sub dc_b30 464"
  by (dc_eval dc_c30_0464)

lemma dc_c30_0465: "dc_sub dc_b30 465"
  by (dc_eval dc_c30_0465)

lemma dc_c30_0466: "dc_sub dc_b30 466"
  by (dc_eval dc_c30_0466)

lemma dc_c30_0467: "dc_sub dc_b30 467"
  by (dc_eval dc_c30_0467)

lemma dc_c30_0468: "dc_sub dc_b30 468"
  by (dc_eval dc_c30_0468)

lemma dc_c30_0469: "dc_sub dc_b30 469"
  by (dc_eval dc_c30_0469)

lemma dc_c30_0470: "dc_sub dc_b30 470"
  by (dc_eval dc_c30_0470)

lemma dc_c30_0471: "dc_sub dc_b30 471"
  by (dc_eval dc_c30_0471)

lemma dc_c30_0472: "dc_sub dc_b30 472"
  by (dc_eval dc_c30_0472)

lemma dc_c30_0473: "dc_sub dc_b30 473"
  by (dc_eval dc_c30_0473)

lemma dc_c30_0474: "dc_sub dc_b30 474"
  by (dc_eval dc_c30_0474)

lemma dc_c30_0475: "dc_sub dc_b30 475"
  by (dc_eval dc_c30_0475)

lemma dc_c30_0476: "dc_sub dc_b30 476"
  by (dc_eval dc_c30_0476)

lemma dc_c30_0477: "dc_sub dc_b30 477"
  by (dc_eval dc_c30_0477)

lemma dc_c30_0478: "dc_sub dc_b30 478"
  by (dc_eval dc_c30_0478)

lemma dc_c30_0479: "dc_sub dc_b30 479"
  by (dc_eval dc_c30_0479)

lemma upt_c30_029: "[464..<480] = [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]"
  by (simp add: upt_rec)

lemma sec_c30_029: "\<forall>j\<in>{16 * 29..<16 * 29 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 29..<16 * 29 + 16}"
  then have "j \<in> set [464..<480]" unfolding set_upt by simp
  then have "j \<in> set [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]" unfolding upt_c30_029 .
  then show "dc_sub dc_b30 j" using dc_c30_0464 dc_c30_0465 dc_c30_0466 dc_c30_0467 dc_c30_0468 dc_c30_0469 dc_c30_0470 dc_c30_0471 dc_c30_0472 dc_c30_0473 dc_c30_0474 dc_c30_0475 dc_c30_0476 dc_c30_0477 dc_c30_0478 dc_c30_0479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
