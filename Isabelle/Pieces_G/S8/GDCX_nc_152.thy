theory GDCX_nc_152
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2432: "gdc_sub None 2432"
  by (gdc_eval gdc_nc_2432)

lemma gdc_nc_2433: "gdc_sub None 2433"
  by (gdc_eval gdc_nc_2433)

lemma gdc_nc_2434: "gdc_sub None 2434"
  by (gdc_eval gdc_nc_2434)

lemma gdc_nc_2435: "gdc_sub None 2435"
  by (gdc_eval gdc_nc_2435)

lemma gdc_nc_2436: "gdc_sub None 2436"
  by (gdc_eval gdc_nc_2436)

lemma gdc_nc_2437: "gdc_sub None 2437"
  by (gdc_eval gdc_nc_2437)

lemma gdc_nc_2438: "gdc_sub None 2438"
  by (gdc_eval gdc_nc_2438)

lemma gdc_nc_2439: "gdc_sub None 2439"
  by (gdc_eval gdc_nc_2439)

lemma gdc_nc_2440: "gdc_sub None 2440"
  by (gdc_eval gdc_nc_2440)

lemma gdc_nc_2441: "gdc_sub None 2441"
  by (gdc_eval gdc_nc_2441)

lemma gdc_nc_2442: "gdc_sub None 2442"
  by (gdc_eval gdc_nc_2442)

lemma gdc_nc_2443: "gdc_sub None 2443"
  by (gdc_eval gdc_nc_2443)

lemma gdc_nc_2444: "gdc_sub None 2444"
  by (gdc_eval gdc_nc_2444)

lemma gdc_nc_2445: "gdc_sub None 2445"
  by (gdc_eval gdc_nc_2445)

lemma gdc_nc_2446: "gdc_sub None 2446"
  by (gdc_eval gdc_nc_2446)

lemma gdc_nc_2447: "gdc_sub None 2447"
  by (gdc_eval gdc_nc_2447)

lemma gupt_nc_152: "[2432..<2448] = [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]"
  by (simp add: upt_rec)

lemma gsec_nc_152: "\<forall>j\<in>{16 * 152..<16 * 152 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 152..<16 * 152 + 16}"
  then have "j \<in> set [2432..<2448]" unfolding set_upt by simp
  then have "j \<in> set [2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447]" unfolding gupt_nc_152 .
  then show "gdc_sub None j" using gdc_nc_2432 gdc_nc_2433 gdc_nc_2434 gdc_nc_2435 gdc_nc_2436 gdc_nc_2437 gdc_nc_2438 gdc_nc_2439 gdc_nc_2440 gdc_nc_2441 gdc_nc_2442 gdc_nc_2443 gdc_nc_2444 gdc_nc_2445 gdc_nc_2446 gdc_nc_2447
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
