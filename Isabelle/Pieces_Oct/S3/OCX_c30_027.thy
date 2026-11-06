theory OCX_c30_027
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0432: "oc_sub oc_b30 432"
  by (oc_eval oc_c30_0432)

lemma oc_c30_0433: "oc_sub oc_b30 433"
  by (oc_eval oc_c30_0433)

lemma oc_c30_0434: "oc_sub oc_b30 434"
  by (oc_eval oc_c30_0434)

lemma oc_c30_0435: "oc_sub oc_b30 435"
  by (oc_eval oc_c30_0435)

lemma oc_c30_0436: "oc_sub oc_b30 436"
  by (oc_eval oc_c30_0436)

lemma oc_c30_0437: "oc_sub oc_b30 437"
  by (oc_eval oc_c30_0437)

lemma oc_c30_0438: "oc_sub oc_b30 438"
  by (oc_eval oc_c30_0438)

lemma oc_c30_0439: "oc_sub oc_b30 439"
  by (oc_eval oc_c30_0439)

lemma oc_c30_0440: "oc_sub oc_b30 440"
  by (oc_eval oc_c30_0440)

lemma oc_c30_0441: "oc_sub oc_b30 441"
  by (oc_eval oc_c30_0441)

lemma oc_c30_0442: "oc_sub oc_b30 442"
  by (oc_eval oc_c30_0442)

lemma oc_c30_0443: "oc_sub oc_b30 443"
  by (oc_eval oc_c30_0443)

lemma oc_c30_0444: "oc_sub oc_b30 444"
  by (oc_eval oc_c30_0444)

lemma oc_c30_0445: "oc_sub oc_b30 445"
  by (oc_eval oc_c30_0445)

lemma oc_c30_0446: "oc_sub oc_b30 446"
  by (oc_eval oc_c30_0446)

lemma oc_c30_0447: "oc_sub oc_b30 447"
  by (oc_eval oc_c30_0447)

lemma upt_c30_027: "[432..<448] = [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]"
  by (simp add: upt_rec)

lemma sec_c30_027: "\<forall>j\<in>{16 * 27..<16 * 27 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 27..<16 * 27 + 16}"
  then have "j \<in> set [432..<448]" unfolding set_upt by simp
  then have "j \<in> set [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]" unfolding upt_c30_027 .
  then show "oc_sub oc_b30 j" using oc_c30_0432 oc_c30_0433 oc_c30_0434 oc_c30_0435 oc_c30_0436 oc_c30_0437 oc_c30_0438 oc_c30_0439 oc_c30_0440 oc_c30_0441 oc_c30_0442 oc_c30_0443 oc_c30_0444 oc_c30_0445 oc_c30_0446 oc_c30_0447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
