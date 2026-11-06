theory DCX_nc_029
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0464: "dc_sub None 464"
  by (dc_eval dc_nc_0464)

lemma dc_nc_0465: "dc_sub None 465"
  by (dc_eval dc_nc_0465)

lemma dc_nc_0466: "dc_sub None 466"
  by (dc_eval dc_nc_0466)

lemma dc_nc_0467: "dc_sub None 467"
  by (dc_eval dc_nc_0467)

lemma dc_nc_0468: "dc_sub None 468"
  by (dc_eval dc_nc_0468)

lemma dc_nc_0469: "dc_sub None 469"
  by (dc_eval dc_nc_0469)

lemma dc_nc_0470: "dc_sub None 470"
  by (dc_eval dc_nc_0470)

lemma dc_nc_0471: "dc_sub None 471"
  by (dc_eval dc_nc_0471)

lemma dc_nc_0472: "dc_sub None 472"
  by (dc_eval dc_nc_0472)

lemma dc_nc_0473: "dc_sub None 473"
  by (dc_eval dc_nc_0473)

lemma dc_nc_0474: "dc_sub None 474"
  by (dc_eval dc_nc_0474)

lemma dc_nc_0475: "dc_sub None 475"
  by (dc_eval dc_nc_0475)

lemma dc_nc_0476: "dc_sub None 476"
  by (dc_eval dc_nc_0476)

lemma dc_nc_0477: "dc_sub None 477"
  by (dc_eval dc_nc_0477)

lemma dc_nc_0478: "dc_sub None 478"
  by (dc_eval dc_nc_0478)

lemma dc_nc_0479: "dc_sub None 479"
  by (dc_eval dc_nc_0479)

lemma upt_nc_029: "[464..<480] = [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]"
  by (simp add: upt_rec)

lemma sec_nc_029: "\<forall>j\<in>{16 * 29..<16 * 29 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 29..<16 * 29 + 16}"
  then have "j \<in> set [464..<480]" unfolding set_upt by simp
  then have "j \<in> set [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]" unfolding upt_nc_029 .
  then show "dc_sub None j" using dc_nc_0464 dc_nc_0465 dc_nc_0466 dc_nc_0467 dc_nc_0468 dc_nc_0469 dc_nc_0470 dc_nc_0471 dc_nc_0472 dc_nc_0473 dc_nc_0474 dc_nc_0475 dc_nc_0476 dc_nc_0477 dc_nc_0478 dc_nc_0479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
