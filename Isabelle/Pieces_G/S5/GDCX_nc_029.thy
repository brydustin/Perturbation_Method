theory GDCX_nc_029
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0464: "gdc_sub None 464"
  by (gdc_eval gdc_nc_0464)

lemma gdc_nc_0465: "gdc_sub None 465"
  by (gdc_eval gdc_nc_0465)

lemma gdc_nc_0466: "gdc_sub None 466"
  by (gdc_eval gdc_nc_0466)

lemma gdc_nc_0467: "gdc_sub None 467"
  by (gdc_eval gdc_nc_0467)

lemma gdc_nc_0468: "gdc_sub None 468"
  by (gdc_eval gdc_nc_0468)

lemma gdc_nc_0469: "gdc_sub None 469"
  by (gdc_eval gdc_nc_0469)

lemma gdc_nc_0470: "gdc_sub None 470"
  by (gdc_eval gdc_nc_0470)

lemma gdc_nc_0471: "gdc_sub None 471"
  by (gdc_eval gdc_nc_0471)

lemma gdc_nc_0472: "gdc_sub None 472"
  by (gdc_eval gdc_nc_0472)

lemma gdc_nc_0473: "gdc_sub None 473"
  by (gdc_eval gdc_nc_0473)

lemma gdc_nc_0474: "gdc_sub None 474"
  by (gdc_eval gdc_nc_0474)

lemma gdc_nc_0475: "gdc_sub None 475"
  by (gdc_eval gdc_nc_0475)

lemma gdc_nc_0476: "gdc_sub None 476"
  by (gdc_eval gdc_nc_0476)

lemma gdc_nc_0477: "gdc_sub None 477"
  by (gdc_eval gdc_nc_0477)

lemma gdc_nc_0478: "gdc_sub None 478"
  by (gdc_eval gdc_nc_0478)

lemma gdc_nc_0479: "gdc_sub None 479"
  by (gdc_eval gdc_nc_0479)

lemma gupt_nc_029: "[464..<480] = [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]"
  by (simp add: upt_rec)

lemma gsec_nc_029: "\<forall>j\<in>{16 * 29..<16 * 29 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 29..<16 * 29 + 16}"
  then have "j \<in> set [464..<480]" unfolding set_upt by simp
  then have "j \<in> set [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]" unfolding gupt_nc_029 .
  then show "gdc_sub None j" using gdc_nc_0464 gdc_nc_0465 gdc_nc_0466 gdc_nc_0467 gdc_nc_0468 gdc_nc_0469 gdc_nc_0470 gdc_nc_0471 gdc_nc_0472 gdc_nc_0473 gdc_nc_0474 gdc_nc_0475 gdc_nc_0476 gdc_nc_0477 gdc_nc_0478 gdc_nc_0479
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
