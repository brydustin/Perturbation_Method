theory GDCX_nc_027
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0432: "gdc_sub None 432"
  by (gdc_eval gdc_nc_0432)

lemma gdc_nc_0433: "gdc_sub None 433"
  by (gdc_eval gdc_nc_0433)

lemma gdc_nc_0434: "gdc_sub None 434"
  by (gdc_eval gdc_nc_0434)

lemma gdc_nc_0435: "gdc_sub None 435"
  by (gdc_eval gdc_nc_0435)

lemma gdc_nc_0436: "gdc_sub None 436"
  by (gdc_eval gdc_nc_0436)

lemma gdc_nc_0437: "gdc_sub None 437"
  by (gdc_eval gdc_nc_0437)

lemma gdc_nc_0438: "gdc_sub None 438"
  by (gdc_eval gdc_nc_0438)

lemma gdc_nc_0439: "gdc_sub None 439"
  by (gdc_eval gdc_nc_0439)

lemma gdc_nc_0440: "gdc_sub None 440"
  by (gdc_eval gdc_nc_0440)

lemma gdc_nc_0441: "gdc_sub None 441"
  by (gdc_eval gdc_nc_0441)

lemma gdc_nc_0442: "gdc_sub None 442"
  by (gdc_eval gdc_nc_0442)

lemma gdc_nc_0443: "gdc_sub None 443"
  by (gdc_eval gdc_nc_0443)

lemma gdc_nc_0444: "gdc_sub None 444"
  by (gdc_eval gdc_nc_0444)

lemma gdc_nc_0445: "gdc_sub None 445"
  by (gdc_eval gdc_nc_0445)

lemma gdc_nc_0446: "gdc_sub None 446"
  by (gdc_eval gdc_nc_0446)

lemma gdc_nc_0447: "gdc_sub None 447"
  by (gdc_eval gdc_nc_0447)

lemma gupt_nc_027: "[432..<448] = [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]"
  by (simp add: upt_rec)

lemma gsec_nc_027: "\<forall>j\<in>{16 * 27..<16 * 27 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 27..<16 * 27 + 16}"
  then have "j \<in> set [432..<448]" unfolding set_upt by simp
  then have "j \<in> set [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]" unfolding gupt_nc_027 .
  then show "gdc_sub None j" using gdc_nc_0432 gdc_nc_0433 gdc_nc_0434 gdc_nc_0435 gdc_nc_0436 gdc_nc_0437 gdc_nc_0438 gdc_nc_0439 gdc_nc_0440 gdc_nc_0441 gdc_nc_0442 gdc_nc_0443 gdc_nc_0444 gdc_nc_0445 gdc_nc_0446 gdc_nc_0447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
