theory DCX_nc_031
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0496: "dc_sub None 496"
  by (dc_eval dc_nc_0496)

lemma dc_nc_0497: "dc_sub None 497"
  by (dc_eval dc_nc_0497)

lemma dc_nc_0498: "dc_sub None 498"
  by (dc_eval dc_nc_0498)

lemma dc_nc_0499: "dc_sub None 499"
  by (dc_eval dc_nc_0499)

lemma dc_nc_0500: "dc_sub None 500"
  by (dc_eval dc_nc_0500)

lemma dc_nc_0501: "dc_sub None 501"
  by (dc_eval dc_nc_0501)

lemma dc_nc_0502: "dc_sub None 502"
  by (dc_eval dc_nc_0502)

lemma dc_nc_0503: "dc_sub None 503"
  by (dc_eval dc_nc_0503)

lemma dc_nc_0504: "dc_sub None 504"
  by (dc_eval dc_nc_0504)

lemma dc_nc_0505: "dc_sub None 505"
  by (dc_eval dc_nc_0505)

lemma dc_nc_0506: "dc_sub None 506"
  by (dc_eval dc_nc_0506)

lemma dc_nc_0507: "dc_sub None 507"
  by (dc_eval dc_nc_0507)

lemma dc_nc_0508: "dc_sub None 508"
  by (dc_eval dc_nc_0508)

lemma dc_nc_0509: "dc_sub None 509"
  by (dc_eval dc_nc_0509)

lemma dc_nc_0510: "dc_sub None 510"
  by (dc_eval dc_nc_0510)

lemma dc_nc_0511: "dc_sub None 511"
  by (dc_eval dc_nc_0511)

lemma upt_nc_031: "[496..<512] = [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]"
  by (simp add: upt_rec)

lemma sec_nc_031: "\<forall>j\<in>{16 * 31..<16 * 31 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 31..<16 * 31 + 16}"
  then have "j \<in> set [496..<512]" unfolding set_upt by simp
  then have "j \<in> set [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]" unfolding upt_nc_031 .
  then show "dc_sub None j" using dc_nc_0496 dc_nc_0497 dc_nc_0498 dc_nc_0499 dc_nc_0500 dc_nc_0501 dc_nc_0502 dc_nc_0503 dc_nc_0504 dc_nc_0505 dc_nc_0506 dc_nc_0507 dc_nc_0508 dc_nc_0509 dc_nc_0510 dc_nc_0511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
