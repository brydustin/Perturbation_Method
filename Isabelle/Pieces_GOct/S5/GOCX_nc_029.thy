theory GOCX_nc_029
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0464: "goc_sub None 464"
  by (goc_eval goc_nc_0464)

lemma goc_nc_0465: "goc_sub None 465"
  by (goc_eval goc_nc_0465)

lemma goc_nc_0466: "goc_sub None 466"
  by (goc_eval goc_nc_0466)

lemma goc_nc_0467: "goc_sub None 467"
  by (goc_eval goc_nc_0467)

lemma goc_nc_0468: "goc_sub None 468"
  by (goc_eval goc_nc_0468)

lemma goc_nc_0469: "goc_sub None 469"
  by (goc_eval goc_nc_0469)

lemma goc_nc_0470: "goc_sub None 470"
  by (goc_eval goc_nc_0470)

lemma goc_nc_0471: "goc_sub None 471"
  by (goc_eval goc_nc_0471)

lemma goc_nc_0472: "goc_sub None 472"
  by (goc_eval goc_nc_0472)

lemma goc_nc_0473: "goc_sub None 473"
  by (goc_eval goc_nc_0473)

lemma goc_nc_0474: "goc_sub None 474"
  by (goc_eval goc_nc_0474)

lemma goc_nc_0475: "goc_sub None 475"
  by (goc_eval goc_nc_0475)

lemma goc_nc_0476: "goc_sub None 476"
  by (goc_eval goc_nc_0476)

lemma goc_nc_0477: "goc_sub None 477"
  by (goc_eval goc_nc_0477)

lemma goc_nc_0478: "goc_sub None 478"
  by (goc_eval goc_nc_0478)

lemma goc_nc_0479: "goc_sub None 479"
  by (goc_eval goc_nc_0479)

lemma gupt_nc_029: "[464..<480] = [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]"
  by (simp add: upt_rec)

lemma gsec_nc_029: "\<forall>j\<in>{16 * 29..<16 * 29 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 29..<16 * 29 + 16}"
  then have "j \<in> set [464..<480]" unfolding set_upt by simp
  then have "j \<in> set [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]" unfolding gupt_nc_029 .
  then show "goc_sub None j" using goc_nc_0464 goc_nc_0465 goc_nc_0466 goc_nc_0467 goc_nc_0468 goc_nc_0469 goc_nc_0470 goc_nc_0471 goc_nc_0472 goc_nc_0473 goc_nc_0474 goc_nc_0475 goc_nc_0476 goc_nc_0477 goc_nc_0478 goc_nc_0479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
