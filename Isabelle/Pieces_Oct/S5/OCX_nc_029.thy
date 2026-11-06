theory OCX_nc_029
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0464: "oc_sub None 464"
  by (oc_eval oc_nc_0464)

lemma oc_nc_0465: "oc_sub None 465"
  by (oc_eval oc_nc_0465)

lemma oc_nc_0466: "oc_sub None 466"
  by (oc_eval oc_nc_0466)

lemma oc_nc_0467: "oc_sub None 467"
  by (oc_eval oc_nc_0467)

lemma oc_nc_0468: "oc_sub None 468"
  by (oc_eval oc_nc_0468)

lemma oc_nc_0469: "oc_sub None 469"
  by (oc_eval oc_nc_0469)

lemma oc_nc_0470: "oc_sub None 470"
  by (oc_eval oc_nc_0470)

lemma oc_nc_0471: "oc_sub None 471"
  by (oc_eval oc_nc_0471)

lemma oc_nc_0472: "oc_sub None 472"
  by (oc_eval oc_nc_0472)

lemma oc_nc_0473: "oc_sub None 473"
  by (oc_eval oc_nc_0473)

lemma oc_nc_0474: "oc_sub None 474"
  by (oc_eval oc_nc_0474)

lemma oc_nc_0475: "oc_sub None 475"
  by (oc_eval oc_nc_0475)

lemma oc_nc_0476: "oc_sub None 476"
  by (oc_eval oc_nc_0476)

lemma oc_nc_0477: "oc_sub None 477"
  by (oc_eval oc_nc_0477)

lemma oc_nc_0478: "oc_sub None 478"
  by (oc_eval oc_nc_0478)

lemma oc_nc_0479: "oc_sub None 479"
  by (oc_eval oc_nc_0479)

lemma upt_nc_029: "[464..<480] = [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]"
  by (simp add: upt_rec)

lemma sec_nc_029: "\<forall>j\<in>{16 * 29..<16 * 29 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 29..<16 * 29 + 16}"
  then have "j \<in> set [464..<480]" unfolding set_upt by simp
  then have "j \<in> set [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]" unfolding upt_nc_029 .
  then show "oc_sub None j" using oc_nc_0464 oc_nc_0465 oc_nc_0466 oc_nc_0467 oc_nc_0468 oc_nc_0469 oc_nc_0470 oc_nc_0471 oc_nc_0472 oc_nc_0473 oc_nc_0474 oc_nc_0475 oc_nc_0476 oc_nc_0477 oc_nc_0478 oc_nc_0479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
