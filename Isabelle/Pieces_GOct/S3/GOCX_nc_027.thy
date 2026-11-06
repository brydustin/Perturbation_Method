theory GOCX_nc_027
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0432: "goc_sub None 432"
  by (goc_eval goc_nc_0432)

lemma goc_nc_0433: "goc_sub None 433"
  by (goc_eval goc_nc_0433)

lemma goc_nc_0434: "goc_sub None 434"
  by (goc_eval goc_nc_0434)

lemma goc_nc_0435: "goc_sub None 435"
  by (goc_eval goc_nc_0435)

lemma goc_nc_0436: "goc_sub None 436"
  by (goc_eval goc_nc_0436)

lemma goc_nc_0437: "goc_sub None 437"
  by (goc_eval goc_nc_0437)

lemma goc_nc_0438: "goc_sub None 438"
  by (goc_eval goc_nc_0438)

lemma goc_nc_0439: "goc_sub None 439"
  by (goc_eval goc_nc_0439)

lemma goc_nc_0440: "goc_sub None 440"
  by (goc_eval goc_nc_0440)

lemma goc_nc_0441: "goc_sub None 441"
  by (goc_eval goc_nc_0441)

lemma goc_nc_0442: "goc_sub None 442"
  by (goc_eval goc_nc_0442)

lemma goc_nc_0443: "goc_sub None 443"
  by (goc_eval goc_nc_0443)

lemma goc_nc_0444: "goc_sub None 444"
  by (goc_eval goc_nc_0444)

lemma goc_nc_0445: "goc_sub None 445"
  by (goc_eval goc_nc_0445)

lemma goc_nc_0446: "goc_sub None 446"
  by (goc_eval goc_nc_0446)

lemma goc_nc_0447: "goc_sub None 447"
  by (goc_eval goc_nc_0447)

lemma gupt_nc_027: "[432..<448] = [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]"
  by (simp add: upt_rec)

lemma gsec_nc_027: "\<forall>j\<in>{16 * 27..<16 * 27 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 27..<16 * 27 + 16}"
  then have "j \<in> set [432..<448]" unfolding set_upt by simp
  then have "j \<in> set [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]" unfolding gupt_nc_027 .
  then show "goc_sub None j" using goc_nc_0432 goc_nc_0433 goc_nc_0434 goc_nc_0435 goc_nc_0436 goc_nc_0437 goc_nc_0438 goc_nc_0439 goc_nc_0440 goc_nc_0441 goc_nc_0442 goc_nc_0443 goc_nc_0444 goc_nc_0445 goc_nc_0446 goc_nc_0447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
