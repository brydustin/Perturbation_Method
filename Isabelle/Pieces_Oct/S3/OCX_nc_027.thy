theory OCX_nc_027
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0432: "oc_sub None 432"
  by (oc_eval oc_nc_0432)

lemma oc_nc_0433: "oc_sub None 433"
  by (oc_eval oc_nc_0433)

lemma oc_nc_0434: "oc_sub None 434"
  by (oc_eval oc_nc_0434)

lemma oc_nc_0435: "oc_sub None 435"
  by (oc_eval oc_nc_0435)

lemma oc_nc_0436: "oc_sub None 436"
  by (oc_eval oc_nc_0436)

lemma oc_nc_0437: "oc_sub None 437"
  by (oc_eval oc_nc_0437)

lemma oc_nc_0438: "oc_sub None 438"
  by (oc_eval oc_nc_0438)

lemma oc_nc_0439: "oc_sub None 439"
  by (oc_eval oc_nc_0439)

lemma oc_nc_0440: "oc_sub None 440"
  by (oc_eval oc_nc_0440)

lemma oc_nc_0441: "oc_sub None 441"
  by (oc_eval oc_nc_0441)

lemma oc_nc_0442: "oc_sub None 442"
  by (oc_eval oc_nc_0442)

lemma oc_nc_0443: "oc_sub None 443"
  by (oc_eval oc_nc_0443)

lemma oc_nc_0444: "oc_sub None 444"
  by (oc_eval oc_nc_0444)

lemma oc_nc_0445: "oc_sub None 445"
  by (oc_eval oc_nc_0445)

lemma oc_nc_0446: "oc_sub None 446"
  by (oc_eval oc_nc_0446)

lemma oc_nc_0447: "oc_sub None 447"
  by (oc_eval oc_nc_0447)

lemma upt_nc_027: "[432..<448] = [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]"
  by (simp add: upt_rec)

lemma sec_nc_027: "\<forall>j\<in>{16 * 27..<16 * 27 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 27..<16 * 27 + 16}"
  then have "j \<in> set [432..<448]" unfolding set_upt by simp
  then have "j \<in> set [432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447]" unfolding upt_nc_027 .
  then show "oc_sub None j" using oc_nc_0432 oc_nc_0433 oc_nc_0434 oc_nc_0435 oc_nc_0436 oc_nc_0437 oc_nc_0438 oc_nc_0439 oc_nc_0440 oc_nc_0441 oc_nc_0442 oc_nc_0443 oc_nc_0444 oc_nc_0445 oc_nc_0446 oc_nc_0447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
