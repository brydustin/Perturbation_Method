theory GDCX_nc_156
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2496: "gdc_sub None 2496"
  by (gdc_eval gdc_nc_2496)

lemma gdc_nc_2497: "gdc_sub None 2497"
  by (gdc_eval gdc_nc_2497)

lemma gdc_nc_2498: "gdc_sub None 2498"
  by (gdc_eval gdc_nc_2498)

lemma gdc_nc_2499: "gdc_sub None 2499"
  by (gdc_eval gdc_nc_2499)

lemma gdc_nc_2500: "gdc_sub None 2500"
  by (gdc_eval gdc_nc_2500)

lemma gdc_nc_2501: "gdc_sub None 2501"
  by (gdc_eval gdc_nc_2501)

lemma gdc_nc_2502: "gdc_sub None 2502"
  by (gdc_eval gdc_nc_2502)

lemma gdc_nc_2503: "gdc_sub None 2503"
  by (gdc_eval gdc_nc_2503)

lemma gdc_nc_2504: "gdc_sub None 2504"
  by (gdc_eval gdc_nc_2504)

lemma gdc_nc_2505: "gdc_sub None 2505"
  by (gdc_eval gdc_nc_2505)

lemma gdc_nc_2506: "gdc_sub None 2506"
  by (gdc_eval gdc_nc_2506)

lemma gdc_nc_2507: "gdc_sub None 2507"
  by (gdc_eval gdc_nc_2507)

lemma gdc_nc_2508: "gdc_sub None 2508"
  by (gdc_eval gdc_nc_2508)

lemma gdc_nc_2509: "gdc_sub None 2509"
  by (gdc_eval gdc_nc_2509)

lemma gdc_nc_2510: "gdc_sub None 2510"
  by (gdc_eval gdc_nc_2510)

lemma gdc_nc_2511: "gdc_sub None 2511"
  by (gdc_eval gdc_nc_2511)

lemma gupt_nc_156: "[2496..<2512] = [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]"
  by (simp add: upt_rec)

lemma gsec_nc_156: "\<forall>j\<in>{16 * 156..<16 * 156 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 156..<16 * 156 + 16}"
  then have "j \<in> set [2496..<2512]" unfolding set_upt by simp
  then have "j \<in> set [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]" unfolding gupt_nc_156 .
  then show "gdc_sub None j" using gdc_nc_2496 gdc_nc_2497 gdc_nc_2498 gdc_nc_2499 gdc_nc_2500 gdc_nc_2501 gdc_nc_2502 gdc_nc_2503 gdc_nc_2504 gdc_nc_2505 gdc_nc_2506 gdc_nc_2507 gdc_nc_2508 gdc_nc_2509 gdc_nc_2510 gdc_nc_2511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
