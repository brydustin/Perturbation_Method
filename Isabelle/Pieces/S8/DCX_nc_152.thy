theory DCX_nc_152
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2432: "dc_sub None 2432"
  by (dc_eval dc_nc_2432)

lemma dc_nc_2433: "dc_sub None 2433"
  by (dc_eval dc_nc_2433)

lemma dc_nc_2434: "dc_sub None 2434"
  by (dc_eval dc_nc_2434)

lemma dc_nc_2435: "dc_sub None 2435"
  by (dc_eval dc_nc_2435)

lemma dc_nc_2436: "dc_sub None 2436"
  by (dc_eval dc_nc_2436)

lemma dc_nc_2437: "dc_sub None 2437"
  by (dc_eval dc_nc_2437)

lemma dc_nc_2438: "dc_sub None 2438"
  by (dc_eval dc_nc_2438)

lemma dc_nc_2439: "dc_sub None 2439"
  by (dc_eval dc_nc_2439)

lemma dc_nc_2440: "dc_sub None 2440"
  by (dc_eval dc_nc_2440)

lemma dc_nc_2441: "dc_sub None 2441"
  by (dc_eval dc_nc_2441)

lemma dc_nc_2442: "dc_sub None 2442"
  by (dc_eval dc_nc_2442)

lemma dc_nc_2443: "dc_sub None 2443"
  by (dc_eval dc_nc_2443)

lemma dc_nc_2444: "dc_sub None 2444"
  by (dc_eval dc_nc_2444)

lemma dc_nc_2445: "dc_sub None 2445"
  by (dc_eval dc_nc_2445)

lemma dc_nc_2446: "dc_sub None 2446"
  by (dc_eval dc_nc_2446)

lemma dc_nc_2447: "dc_sub None 2447"
  by (dc_eval dc_nc_2447)

lemma upt_nc_152: "[2432..<2448] = [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]"
  by (simp add: upt_rec)

lemma sec_nc_152: "\<forall>j\<in>{16 * 152..<16 * 152 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 152..<16 * 152 + 16}"
  then have "j \<in> set [2432..<2448]" unfolding set_upt by simp
  then have "j \<in> set [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]" unfolding upt_nc_152 .
  then show "dc_sub None j" using dc_nc_2432 dc_nc_2433 dc_nc_2434 dc_nc_2435 dc_nc_2436 dc_nc_2437 dc_nc_2438 dc_nc_2439 dc_nc_2440 dc_nc_2441 dc_nc_2442 dc_nc_2443 dc_nc_2444 dc_nc_2445 dc_nc_2446 dc_nc_2447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
