theory OCX_nc_152
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2432: "oc_sub None 2432"
  by (oc_eval oc_nc_2432)

lemma oc_nc_2433: "oc_sub None 2433"
  by (oc_eval oc_nc_2433)

lemma oc_nc_2434: "oc_sub None 2434"
  by (oc_eval oc_nc_2434)

lemma oc_nc_2435: "oc_sub None 2435"
  by (oc_eval oc_nc_2435)

lemma oc_nc_2436: "oc_sub None 2436"
  by (oc_eval oc_nc_2436)

lemma oc_nc_2437: "oc_sub None 2437"
  by (oc_eval oc_nc_2437)

lemma oc_nc_2438: "oc_sub None 2438"
  by (oc_eval oc_nc_2438)

lemma oc_nc_2439: "oc_sub None 2439"
  by (oc_eval oc_nc_2439)

lemma oc_nc_2440: "oc_sub None 2440"
  by (oc_eval oc_nc_2440)

lemma oc_nc_2441: "oc_sub None 2441"
  by (oc_eval oc_nc_2441)

lemma oc_nc_2442: "oc_sub None 2442"
  by (oc_eval oc_nc_2442)

lemma oc_nc_2443: "oc_sub None 2443"
  by (oc_eval oc_nc_2443)

lemma oc_nc_2444: "oc_sub None 2444"
  by (oc_eval oc_nc_2444)

lemma oc_nc_2445: "oc_sub None 2445"
  by (oc_eval oc_nc_2445)

lemma oc_nc_2446: "oc_sub None 2446"
  by (oc_eval oc_nc_2446)

lemma oc_nc_2447: "oc_sub None 2447"
  by (oc_eval oc_nc_2447)

lemma upt_nc_152: "[2432..<2448] = [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]"
  by (simp add: upt_rec)

lemma sec_nc_152: "\<forall>j\<in>{16 * 152..<16 * 152 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 152..<16 * 152 + 16}"
  then have "j \<in> set [2432..<2448]" unfolding set_upt by simp
  then have "j \<in> set [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]" unfolding upt_nc_152 .
  then show "oc_sub None j" using oc_nc_2432 oc_nc_2433 oc_nc_2434 oc_nc_2435 oc_nc_2436 oc_nc_2437 oc_nc_2438 oc_nc_2439 oc_nc_2440 oc_nc_2441 oc_nc_2442 oc_nc_2443 oc_nc_2444 oc_nc_2445 oc_nc_2446 oc_nc_2447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
