theory OCX_c30_153
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2448: "oc_sub oc_b30 2448"
  by (oc_eval oc_c30_2448)

lemma oc_c30_2449: "oc_sub oc_b30 2449"
  by (oc_eval oc_c30_2449)

lemma oc_c30_2450: "oc_sub oc_b30 2450"
  by (oc_eval oc_c30_2450)

lemma oc_c30_2451: "oc_sub oc_b30 2451"
  by (oc_eval oc_c30_2451)

lemma oc_c30_2452: "oc_sub oc_b30 2452"
  by (oc_eval oc_c30_2452)

lemma oc_c30_2453: "oc_sub oc_b30 2453"
  by (oc_eval oc_c30_2453)

lemma oc_c30_2454: "oc_sub oc_b30 2454"
  by (oc_eval oc_c30_2454)

lemma oc_c30_2455: "oc_sub oc_b30 2455"
  by (oc_eval oc_c30_2455)

lemma oc_c30_2456: "oc_sub oc_b30 2456"
  by (oc_eval oc_c30_2456)

lemma oc_c30_2457: "oc_sub oc_b30 2457"
  by (oc_eval oc_c30_2457)

lemma oc_c30_2458: "oc_sub oc_b30 2458"
  by (oc_eval oc_c30_2458)

lemma oc_c30_2459: "oc_sub oc_b30 2459"
  by (oc_eval oc_c30_2459)

lemma oc_c30_2460: "oc_sub oc_b30 2460"
  by (oc_eval oc_c30_2460)

lemma oc_c30_2461: "oc_sub oc_b30 2461"
  by (oc_eval oc_c30_2461)

lemma oc_c30_2462: "oc_sub oc_b30 2462"
  by (oc_eval oc_c30_2462)

lemma oc_c30_2463: "oc_sub oc_b30 2463"
  by (oc_eval oc_c30_2463)

lemma upt_c30_153: "[2448..<2464] = [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]"
  by (simp add: upt_rec)

lemma sec_c30_153: "\<forall>j\<in>{16 * 153..<16 * 153 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 153..<16 * 153 + 16}"
  then have "j \<in> set [2448..<2464]" unfolding set_upt by simp
  then have "j \<in> set [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]" unfolding upt_c30_153 .
  then show "oc_sub oc_b30 j" using oc_c30_2448 oc_c30_2449 oc_c30_2450 oc_c30_2451 oc_c30_2452 oc_c30_2453 oc_c30_2454 oc_c30_2455 oc_c30_2456 oc_c30_2457 oc_c30_2458 oc_c30_2459 oc_c30_2460 oc_c30_2461 oc_c30_2462 oc_c30_2463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
