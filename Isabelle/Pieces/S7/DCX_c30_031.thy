theory DCX_c30_031
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0496: "dc_sub dc_b30 496"
  by (dc_eval dc_c30_0496)

lemma dc_c30_0497: "dc_sub dc_b30 497"
  by (dc_eval dc_c30_0497)

lemma dc_c30_0498: "dc_sub dc_b30 498"
  by (dc_eval dc_c30_0498)

lemma dc_c30_0499: "dc_sub dc_b30 499"
  by (dc_eval dc_c30_0499)

lemma dc_c30_0500: "dc_sub dc_b30 500"
  by (dc_eval dc_c30_0500)

lemma dc_c30_0501: "dc_sub dc_b30 501"
  by (dc_eval dc_c30_0501)

lemma dc_c30_0502: "dc_sub dc_b30 502"
  by (dc_eval dc_c30_0502)

lemma dc_c30_0503: "dc_sub dc_b30 503"
  by (dc_eval dc_c30_0503)

lemma dc_c30_0504: "dc_sub dc_b30 504"
  by (dc_eval dc_c30_0504)

lemma dc_c30_0505: "dc_sub dc_b30 505"
  by (dc_eval dc_c30_0505)

lemma dc_c30_0506: "dc_sub dc_b30 506"
  by (dc_eval dc_c30_0506)

lemma dc_c30_0507: "dc_sub dc_b30 507"
  by (dc_eval dc_c30_0507)

lemma dc_c30_0508: "dc_sub dc_b30 508"
  by (dc_eval dc_c30_0508)

lemma dc_c30_0509: "dc_sub dc_b30 509"
  by (dc_eval dc_c30_0509)

lemma dc_c30_0510: "dc_sub dc_b30 510"
  by (dc_eval dc_c30_0510)

lemma dc_c30_0511: "dc_sub dc_b30 511"
  by (dc_eval dc_c30_0511)

lemma upt_c30_031: "[496..<512] = [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]"
  by (simp add: upt_rec)

lemma sec_c30_031: "\<forall>j\<in>{16 * 31..<16 * 31 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 31..<16 * 31 + 16}"
  then have "j \<in> set [496..<512]" unfolding set_upt by simp
  then have "j \<in> set [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]" unfolding upt_c30_031 .
  then show "dc_sub dc_b30 j" using dc_c30_0496 dc_c30_0497 dc_c30_0498 dc_c30_0499 dc_c30_0500 dc_c30_0501 dc_c30_0502 dc_c30_0503 dc_c30_0504 dc_c30_0505 dc_c30_0506 dc_c30_0507 dc_c30_0508 dc_c30_0509 dc_c30_0510 dc_c30_0511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
