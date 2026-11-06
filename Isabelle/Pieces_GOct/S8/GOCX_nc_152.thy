theory GOCX_nc_152
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2432: "goc_sub None 2432"
  by (goc_eval goc_nc_2432)

lemma goc_nc_2433: "goc_sub None 2433"
  by (goc_eval goc_nc_2433)

lemma goc_nc_2434: "goc_sub None 2434"
  by (goc_eval goc_nc_2434)

lemma goc_nc_2435: "goc_sub None 2435"
  by (goc_eval goc_nc_2435)

lemma goc_nc_2436: "goc_sub None 2436"
  by (goc_eval goc_nc_2436)

lemma goc_nc_2437: "goc_sub None 2437"
  by (goc_eval goc_nc_2437)

lemma goc_nc_2438: "goc_sub None 2438"
  by (goc_eval goc_nc_2438)

lemma goc_nc_2439: "goc_sub None 2439"
  by (goc_eval goc_nc_2439)

lemma goc_nc_2440: "goc_sub None 2440"
  by (goc_eval goc_nc_2440)

lemma goc_nc_2441: "goc_sub None 2441"
  by (goc_eval goc_nc_2441)

lemma goc_nc_2442: "goc_sub None 2442"
  by (goc_eval goc_nc_2442)

lemma goc_nc_2443: "goc_sub None 2443"
  by (goc_eval goc_nc_2443)

lemma goc_nc_2444: "goc_sub None 2444"
  by (goc_eval goc_nc_2444)

lemma goc_nc_2445: "goc_sub None 2445"
  by (goc_eval goc_nc_2445)

lemma goc_nc_2446: "goc_sub None 2446"
  by (goc_eval goc_nc_2446)

lemma goc_nc_2447: "goc_sub None 2447"
  by (goc_eval goc_nc_2447)

lemma gupt_nc_152: "[2432..<2448] = [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]"
  by (simp add: upt_rec)

lemma gsec_nc_152: "\<forall>j\<in>{16 * 152..<16 * 152 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 152..<16 * 152 + 16}"
  then have "j \<in> set [2432..<2448]" unfolding set_upt by simp
  then have "j \<in> set [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]" unfolding gupt_nc_152 .
  then show "goc_sub None j" using goc_nc_2432 goc_nc_2433 goc_nc_2434 goc_nc_2435 goc_nc_2436 goc_nc_2437 goc_nc_2438 goc_nc_2439 goc_nc_2440 goc_nc_2441 goc_nc_2442 goc_nc_2443 goc_nc_2444 goc_nc_2445 goc_nc_2446 goc_nc_2447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
