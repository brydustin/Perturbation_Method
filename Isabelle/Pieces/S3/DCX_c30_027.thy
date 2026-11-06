theory DCX_c30_027
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0432: "dc_sub dc_b30 432"
  by (dc_eval dc_c30_0432)

lemma dc_c30_0433: "dc_sub dc_b30 433"
  by (dc_eval dc_c30_0433)

lemma dc_c30_0434: "dc_sub dc_b30 434"
  by (dc_eval dc_c30_0434)

lemma dc_c30_0435: "dc_sub dc_b30 435"
  by (dc_eval dc_c30_0435)

lemma dc_c30_0436: "dc_sub dc_b30 436"
  by (dc_eval dc_c30_0436)

lemma dc_c30_0437: "dc_sub dc_b30 437"
  by (dc_eval dc_c30_0437)

lemma dc_c30_0438: "dc_sub dc_b30 438"
  by (dc_eval dc_c30_0438)

lemma dc_c30_0439: "dc_sub dc_b30 439"
  by (dc_eval dc_c30_0439)

lemma dc_c30_0440: "dc_sub dc_b30 440"
  by (dc_eval dc_c30_0440)

lemma dc_c30_0441: "dc_sub dc_b30 441"
  by (dc_eval dc_c30_0441)

lemma dc_c30_0442: "dc_sub dc_b30 442"
  by (dc_eval dc_c30_0442)

lemma dc_c30_0443: "dc_sub dc_b30 443"
  by (dc_eval dc_c30_0443)

lemma dc_c30_0444: "dc_sub dc_b30 444"
  by (dc_eval dc_c30_0444)

lemma dc_c30_0445: "dc_sub dc_b30 445"
  by (dc_eval dc_c30_0445)

lemma dc_c30_0446: "dc_sub dc_b30 446"
  by (dc_eval dc_c30_0446)

lemma dc_c30_0447: "dc_sub dc_b30 447"
  by (dc_eval dc_c30_0447)

lemma upt_c30_027: "[432..<448] = [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]"
  by (simp add: upt_rec)

lemma sec_c30_027: "\<forall>j\<in>{16 * 27..<16 * 27 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 27..<16 * 27 + 16}"
  then have "j \<in> set [432..<448]" unfolding set_upt by simp
  then have "j \<in> set [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]" unfolding upt_c30_027 .
  then show "dc_sub dc_b30 j" using dc_c30_0432 dc_c30_0433 dc_c30_0434 dc_c30_0435 dc_c30_0436 dc_c30_0437 dc_c30_0438 dc_c30_0439 dc_c30_0440 dc_c30_0441 dc_c30_0442 dc_c30_0443 dc_c30_0444 dc_c30_0445 dc_c30_0446 dc_c30_0447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
