theory DCX_c30_152
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2432: "dc_sub dc_b30 2432"
  by (dc_eval dc_c30_2432)

lemma dc_c30_2433: "dc_sub dc_b30 2433"
  by (dc_eval dc_c30_2433)

lemma dc_c30_2434: "dc_sub dc_b30 2434"
  by (dc_eval dc_c30_2434)

lemma dc_c30_2435: "dc_sub dc_b30 2435"
  by (dc_eval dc_c30_2435)

lemma dc_c30_2436: "dc_sub dc_b30 2436"
  by (dc_eval dc_c30_2436)

lemma dc_c30_2437: "dc_sub dc_b30 2437"
  by (dc_eval dc_c30_2437)

lemma dc_c30_2438: "dc_sub dc_b30 2438"
  by (dc_eval dc_c30_2438)

lemma dc_c30_2439: "dc_sub dc_b30 2439"
  by (dc_eval dc_c30_2439)

lemma dc_c30_2440: "dc_sub dc_b30 2440"
  by (dc_eval dc_c30_2440)

lemma dc_c30_2441: "dc_sub dc_b30 2441"
  by (dc_eval dc_c30_2441)

lemma dc_c30_2442: "dc_sub dc_b30 2442"
  by (dc_eval dc_c30_2442)

lemma dc_c30_2443: "dc_sub dc_b30 2443"
  by (dc_eval dc_c30_2443)

lemma dc_c30_2444: "dc_sub dc_b30 2444"
  by (dc_eval dc_c30_2444)

lemma dc_c30_2445: "dc_sub dc_b30 2445"
  by (dc_eval dc_c30_2445)

lemma dc_c30_2446: "dc_sub dc_b30 2446"
  by (dc_eval dc_c30_2446)

lemma dc_c30_2447: "dc_sub dc_b30 2447"
  by (dc_eval dc_c30_2447)

lemma upt_c30_152: "[2432..<2448] = [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]"
  by (simp add: upt_rec)

lemma sec_c30_152: "\<forall>j\<in>{16 * 152..<16 * 152 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 152..<16 * 152 + 16}"
  then have "j \<in> set [2432..<2448]" unfolding set_upt by simp
  then have "j \<in> set [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]" unfolding upt_c30_152 .
  then show "dc_sub dc_b30 j" using dc_c30_2432 dc_c30_2433 dc_c30_2434 dc_c30_2435 dc_c30_2436 dc_c30_2437 dc_c30_2438 dc_c30_2439 dc_c30_2440 dc_c30_2441 dc_c30_2442 dc_c30_2443 dc_c30_2444 dc_c30_2445 dc_c30_2446 dc_c30_2447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
