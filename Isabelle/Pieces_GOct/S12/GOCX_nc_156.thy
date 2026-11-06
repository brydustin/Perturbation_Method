theory GOCX_nc_156
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2496: "goc_sub None 2496"
  by (goc_eval goc_nc_2496)

lemma goc_nc_2497: "goc_sub None 2497"
  by (goc_eval goc_nc_2497)

lemma goc_nc_2498: "goc_sub None 2498"
  by (goc_eval goc_nc_2498)

lemma goc_nc_2499: "goc_sub None 2499"
  by (goc_eval goc_nc_2499)

lemma goc_nc_2500: "goc_sub None 2500"
  by (goc_eval goc_nc_2500)

lemma goc_nc_2501: "goc_sub None 2501"
  by (goc_eval goc_nc_2501)

lemma goc_nc_2502: "goc_sub None 2502"
  by (goc_eval goc_nc_2502)

lemma goc_nc_2503: "goc_sub None 2503"
  by (goc_eval goc_nc_2503)

lemma goc_nc_2504: "goc_sub None 2504"
  by (goc_eval goc_nc_2504)

lemma goc_nc_2505: "goc_sub None 2505"
  by (goc_eval goc_nc_2505)

lemma goc_nc_2506: "goc_sub None 2506"
  by (goc_eval goc_nc_2506)

lemma goc_nc_2507: "goc_sub None 2507"
  by (goc_eval goc_nc_2507)

lemma goc_nc_2508: "goc_sub None 2508"
  by (goc_eval goc_nc_2508)

lemma goc_nc_2509: "goc_sub None 2509"
  by (goc_eval goc_nc_2509)

lemma goc_nc_2510: "goc_sub None 2510"
  by (goc_eval goc_nc_2510)

lemma goc_nc_2511: "goc_sub None 2511"
  by (goc_eval goc_nc_2511)

lemma gupt_nc_156: "[2496..<2512] = [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]"
  by (simp add: upt_rec)

lemma gsec_nc_156: "\<forall>j\<in>{16 * 156..<16 * 156 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 156..<16 * 156 + 16}"
  then have "j \<in> set [2496..<2512]" unfolding set_upt by simp
  then have "j \<in> set [2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511]" unfolding gupt_nc_156 .
  then show "goc_sub None j" using goc_nc_2496 goc_nc_2497 goc_nc_2498 goc_nc_2499 goc_nc_2500 goc_nc_2501 goc_nc_2502 goc_nc_2503 goc_nc_2504 goc_nc_2505 goc_nc_2506 goc_nc_2507 goc_nc_2508 goc_nc_2509 goc_nc_2510 goc_nc_2511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
