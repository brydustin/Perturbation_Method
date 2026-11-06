theory DCX_nc_156
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2496: "dc_sub None 2496"
  by (dc_eval dc_nc_2496)

lemma dc_nc_2497: "dc_sub None 2497"
  by (dc_eval dc_nc_2497)

lemma dc_nc_2498: "dc_sub None 2498"
  by (dc_eval dc_nc_2498)

lemma dc_nc_2499: "dc_sub None 2499"
  by (dc_eval dc_nc_2499)

lemma dc_nc_2500: "dc_sub None 2500"
  by (dc_eval dc_nc_2500)

lemma dc_nc_2501: "dc_sub None 2501"
  by (dc_eval dc_nc_2501)

lemma dc_nc_2502: "dc_sub None 2502"
  by (dc_eval dc_nc_2502)

lemma dc_nc_2503: "dc_sub None 2503"
  by (dc_eval dc_nc_2503)

lemma dc_nc_2504: "dc_sub None 2504"
  by (dc_eval dc_nc_2504)

lemma dc_nc_2505: "dc_sub None 2505"
  by (dc_eval dc_nc_2505)

lemma dc_nc_2506: "dc_sub None 2506"
  by (dc_eval dc_nc_2506)

lemma dc_nc_2507: "dc_sub None 2507"
  by (dc_eval dc_nc_2507)

lemma dc_nc_2508: "dc_sub None 2508"
  by (dc_eval dc_nc_2508)

lemma dc_nc_2509: "dc_sub None 2509"
  by (dc_eval dc_nc_2509)

lemma dc_nc_2510: "dc_sub None 2510"
  by (dc_eval dc_nc_2510)

lemma dc_nc_2511: "dc_sub None 2511"
  by (dc_eval dc_nc_2511)

lemma upt_nc_156: "[2496..<2512] = [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]"
  by (simp add: upt_rec)

lemma sec_nc_156: "\<forall>j\<in>{16 * 156..<16 * 156 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 156..<16 * 156 + 16}"
  then have "j \<in> set [2496..<2512]" unfolding set_upt by simp
  then have "j \<in> set [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]" unfolding upt_nc_156 .
  then show "dc_sub None j" using dc_nc_2496 dc_nc_2497 dc_nc_2498 dc_nc_2499 dc_nc_2500 dc_nc_2501 dc_nc_2502 dc_nc_2503 dc_nc_2504 dc_nc_2505 dc_nc_2506 dc_nc_2507 dc_nc_2508 dc_nc_2509 dc_nc_2510 dc_nc_2511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
