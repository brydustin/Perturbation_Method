theory OCX_nc_153
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2448: "oc_sub None 2448"
  by (oc_eval oc_nc_2448)

lemma oc_nc_2449: "oc_sub None 2449"
  by (oc_eval oc_nc_2449)

lemma oc_nc_2450: "oc_sub None 2450"
  by (oc_eval oc_nc_2450)

lemma oc_nc_2451: "oc_sub None 2451"
  by (oc_eval oc_nc_2451)

lemma oc_nc_2452: "oc_sub None 2452"
  by (oc_eval oc_nc_2452)

lemma oc_nc_2453: "oc_sub None 2453"
  by (oc_eval oc_nc_2453)

lemma oc_nc_2454: "oc_sub None 2454"
  by (oc_eval oc_nc_2454)

lemma oc_nc_2455: "oc_sub None 2455"
  by (oc_eval oc_nc_2455)

lemma oc_nc_2456: "oc_sub None 2456"
  by (oc_eval oc_nc_2456)

lemma oc_nc_2457: "oc_sub None 2457"
  by (oc_eval oc_nc_2457)

lemma oc_nc_2458: "oc_sub None 2458"
  by (oc_eval oc_nc_2458)

lemma oc_nc_2459: "oc_sub None 2459"
  by (oc_eval oc_nc_2459)

lemma oc_nc_2460: "oc_sub None 2460"
  by (oc_eval oc_nc_2460)

lemma oc_nc_2461: "oc_sub None 2461"
  by (oc_eval oc_nc_2461)

lemma oc_nc_2462: "oc_sub None 2462"
  by (oc_eval oc_nc_2462)

lemma oc_nc_2463: "oc_sub None 2463"
  by (oc_eval oc_nc_2463)

lemma upt_nc_153: "[2448..<2464] = [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]"
  by (simp add: upt_rec)

lemma sec_nc_153: "\<forall>j\<in>{16 * 153..<16 * 153 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 153..<16 * 153 + 16}"
  then have "j \<in> set [2448..<2464]" unfolding set_upt by simp
  then have "j \<in> set [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]" unfolding upt_nc_153 .
  then show "oc_sub None j" using oc_nc_2448 oc_nc_2449 oc_nc_2450 oc_nc_2451 oc_nc_2452 oc_nc_2453 oc_nc_2454 oc_nc_2455 oc_nc_2456 oc_nc_2457 oc_nc_2458 oc_nc_2459 oc_nc_2460 oc_nc_2461 oc_nc_2462 oc_nc_2463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
