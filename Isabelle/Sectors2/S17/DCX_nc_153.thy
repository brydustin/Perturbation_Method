theory DCX_nc_153
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2448: "dc_sub None 2448"
  by (dc_eval dc_nc_2448)

lemma dc_nc_2449: "dc_sub None 2449"
  by (dc_eval dc_nc_2449)

lemma dc_nc_2450: "dc_sub None 2450"
  by (dc_eval dc_nc_2450)

lemma dc_nc_2451: "dc_sub None 2451"
  by (dc_eval dc_nc_2451)

lemma dc_nc_2452: "dc_sub None 2452"
  by (dc_eval dc_nc_2452)

lemma dc_nc_2453: "dc_sub None 2453"
  by (dc_eval dc_nc_2453)

lemma dc_nc_2454: "dc_sub None 2454"
  by (dc_eval dc_nc_2454)

lemma dc_nc_2455: "dc_sub None 2455"
  by (dc_eval dc_nc_2455)

lemma dc_nc_2456: "dc_sub None 2456"
  by (dc_eval dc_nc_2456)

lemma dc_nc_2457: "dc_sub None 2457"
  by (dc_eval dc_nc_2457)

lemma dc_nc_2458: "dc_sub None 2458"
  by (dc_eval dc_nc_2458)

lemma dc_nc_2459: "dc_sub None 2459"
  by (dc_eval dc_nc_2459)

lemma dc_nc_2460: "dc_sub None 2460"
  by (dc_eval dc_nc_2460)

lemma dc_nc_2461: "dc_sub None 2461"
  by (dc_eval dc_nc_2461)

lemma dc_nc_2462: "dc_sub None 2462"
  by (dc_eval dc_nc_2462)

lemma dc_nc_2463: "dc_sub None 2463"
  by (dc_eval dc_nc_2463)

lemma upt_nc_153: "[2448..<2464] = [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]"
  by (simp add: upt_rec)

lemma sec_nc_153: "\<forall>j\<in>{16 * 153..<16 * 153 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 153..<16 * 153 + 16}"
  then have "j \<in> set [2448..<2464]" unfolding set_upt by simp
  then have "j \<in> set [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]" unfolding upt_nc_153 .
  then show "dc_sub None j" using dc_nc_2448 dc_nc_2449 dc_nc_2450 dc_nc_2451 dc_nc_2452 dc_nc_2453 dc_nc_2454 dc_nc_2455 dc_nc_2456 dc_nc_2457 dc_nc_2458 dc_nc_2459 dc_nc_2460 dc_nc_2461 dc_nc_2462 dc_nc_2463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
