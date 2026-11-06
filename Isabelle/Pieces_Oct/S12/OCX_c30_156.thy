theory OCX_c30_156
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2496: "oc_sub oc_b30 2496"
  by (oc_eval oc_c30_2496)

lemma oc_c30_2497: "oc_sub oc_b30 2497"
  by (oc_eval oc_c30_2497)

lemma oc_c30_2498: "oc_sub oc_b30 2498"
  by (oc_eval oc_c30_2498)

lemma oc_c30_2499: "oc_sub oc_b30 2499"
  by (oc_eval oc_c30_2499)

lemma oc_c30_2500: "oc_sub oc_b30 2500"
  by (oc_eval oc_c30_2500)

lemma oc_c30_2501: "oc_sub oc_b30 2501"
  by (oc_eval oc_c30_2501)

lemma oc_c30_2502: "oc_sub oc_b30 2502"
  by (oc_eval oc_c30_2502)

lemma oc_c30_2503: "oc_sub oc_b30 2503"
  by (oc_eval oc_c30_2503)

lemma oc_c30_2504: "oc_sub oc_b30 2504"
  by (oc_eval oc_c30_2504)

lemma oc_c30_2505: "oc_sub oc_b30 2505"
  by (oc_eval oc_c30_2505)

lemma oc_c30_2506: "oc_sub oc_b30 2506"
  by (oc_eval oc_c30_2506)

lemma oc_c30_2507: "oc_sub oc_b30 2507"
  by (oc_eval oc_c30_2507)

lemma oc_c30_2508: "oc_sub oc_b30 2508"
  by (oc_eval oc_c30_2508)

lemma oc_c30_2509: "oc_sub oc_b30 2509"
  by (oc_eval oc_c30_2509)

lemma oc_c30_2510: "oc_sub oc_b30 2510"
  by (oc_eval oc_c30_2510)

lemma oc_c30_2511: "oc_sub oc_b30 2511"
  by (oc_eval oc_c30_2511)

lemma upt_c30_156: "[2496..<2512] = [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]"
  by (simp add: upt_rec)

lemma sec_c30_156: "\<forall>j\<in>{16 * 156..<16 * 156 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 156..<16 * 156 + 16}"
  then have "j \<in> set [2496..<2512]" unfolding set_upt by simp
  then have "j \<in> set [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]" unfolding upt_c30_156 .
  then show "oc_sub oc_b30 j" using oc_c30_2496 oc_c30_2497 oc_c30_2498 oc_c30_2499 oc_c30_2500 oc_c30_2501 oc_c30_2502 oc_c30_2503 oc_c30_2504 oc_c30_2505 oc_c30_2506 oc_c30_2507 oc_c30_2508 oc_c30_2509 oc_c30_2510 oc_c30_2511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
