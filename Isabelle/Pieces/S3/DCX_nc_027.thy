theory DCX_nc_027
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0432: "dc_sub None 432"
  by (dc_eval dc_nc_0432)

lemma dc_nc_0433: "dc_sub None 433"
  by (dc_eval dc_nc_0433)

lemma dc_nc_0434: "dc_sub None 434"
  by (dc_eval dc_nc_0434)

lemma dc_nc_0435: "dc_sub None 435"
  by (dc_eval dc_nc_0435)

lemma dc_nc_0436: "dc_sub None 436"
  by (dc_eval dc_nc_0436)

lemma dc_nc_0437: "dc_sub None 437"
  by (dc_eval dc_nc_0437)

lemma dc_nc_0438: "dc_sub None 438"
  by (dc_eval dc_nc_0438)

lemma dc_nc_0439: "dc_sub None 439"
  by (dc_eval dc_nc_0439)

lemma dc_nc_0440: "dc_sub None 440"
  by (dc_eval dc_nc_0440)

lemma dc_nc_0441: "dc_sub None 441"
  by (dc_eval dc_nc_0441)

lemma dc_nc_0442: "dc_sub None 442"
  by (dc_eval dc_nc_0442)

lemma dc_nc_0443: "dc_sub None 443"
  by (dc_eval dc_nc_0443)

lemma dc_nc_0444: "dc_sub None 444"
  by (dc_eval dc_nc_0444)

lemma dc_nc_0445: "dc_sub None 445"
  by (dc_eval dc_nc_0445)

lemma dc_nc_0446: "dc_sub None 446"
  by (dc_eval dc_nc_0446)

lemma dc_nc_0447: "dc_sub None 447"
  by (dc_eval dc_nc_0447)

lemma upt_nc_027: "[432..<448] = [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]"
  by (simp add: upt_rec)

lemma sec_nc_027: "\<forall>j\<in>{16 * 27..<16 * 27 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 27..<16 * 27 + 16}"
  then have "j \<in> set [432..<448]" unfolding set_upt by simp
  then have "j \<in> set [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]" unfolding upt_nc_027 .
  then show "dc_sub None j" using dc_nc_0432 dc_nc_0433 dc_nc_0434 dc_nc_0435 dc_nc_0436 dc_nc_0437 dc_nc_0438 dc_nc_0439 dc_nc_0440 dc_nc_0441 dc_nc_0442 dc_nc_0443 dc_nc_0444 dc_nc_0445 dc_nc_0446 dc_nc_0447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
