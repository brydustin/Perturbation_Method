theory DCX_c30_156
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2496: "dc_sub dc_b30 2496"
  by (dc_eval dc_c30_2496)

lemma dc_c30_2497: "dc_sub dc_b30 2497"
  by (dc_eval dc_c30_2497)

lemma dc_c30_2498: "dc_sub dc_b30 2498"
  by (dc_eval dc_c30_2498)

lemma dc_c30_2499: "dc_sub dc_b30 2499"
  by (dc_eval dc_c30_2499)

lemma dc_c30_2500: "dc_sub dc_b30 2500"
  by (dc_eval dc_c30_2500)

lemma dc_c30_2501: "dc_sub dc_b30 2501"
  by (dc_eval dc_c30_2501)

lemma dc_c30_2502: "dc_sub dc_b30 2502"
  by (dc_eval dc_c30_2502)

lemma dc_c30_2503: "dc_sub dc_b30 2503"
  by (dc_eval dc_c30_2503)

lemma dc_c30_2504: "dc_sub dc_b30 2504"
  by (dc_eval dc_c30_2504)

lemma dc_c30_2505: "dc_sub dc_b30 2505"
  by (dc_eval dc_c30_2505)

lemma dc_c30_2506: "dc_sub dc_b30 2506"
  by (dc_eval dc_c30_2506)

lemma dc_c30_2507: "dc_sub dc_b30 2507"
  by (dc_eval dc_c30_2507)

lemma dc_c30_2508: "dc_sub dc_b30 2508"
  by (dc_eval dc_c30_2508)

lemma dc_c30_2509: "dc_sub dc_b30 2509"
  by (dc_eval dc_c30_2509)

lemma dc_c30_2510: "dc_sub dc_b30 2510"
  by (dc_eval dc_c30_2510)

lemma dc_c30_2511: "dc_sub dc_b30 2511"
  by (dc_eval dc_c30_2511)

lemma upt_c30_156: "[2496..<2512] = [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]"
  by (simp add: upt_rec)

lemma sec_c30_156: "\<forall>j\<in>{16 * 156..<16 * 156 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 156..<16 * 156 + 16}"
  then have "j \<in> set [2496..<2512]" unfolding set_upt by simp
  then have "j \<in> set [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]" unfolding upt_c30_156 .
  then show "dc_sub dc_b30 j" using dc_c30_2496 dc_c30_2497 dc_c30_2498 dc_c30_2499 dc_c30_2500 dc_c30_2501 dc_c30_2502 dc_c30_2503 dc_c30_2504 dc_c30_2505 dc_c30_2506 dc_c30_2507 dc_c30_2508 dc_c30_2509 dc_c30_2510 dc_c30_2511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
