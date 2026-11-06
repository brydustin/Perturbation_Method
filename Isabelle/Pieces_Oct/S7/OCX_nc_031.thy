theory OCX_nc_031
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0496: "oc_sub None 496"
  by (oc_eval oc_nc_0496)

lemma oc_nc_0497: "oc_sub None 497"
  by (oc_eval oc_nc_0497)

lemma oc_nc_0498: "oc_sub None 498"
  by (oc_eval oc_nc_0498)

lemma oc_nc_0499: "oc_sub None 499"
  by (oc_eval oc_nc_0499)

lemma oc_nc_0500: "oc_sub None 500"
  by (oc_eval oc_nc_0500)

lemma oc_nc_0501: "oc_sub None 501"
  by (oc_eval oc_nc_0501)

lemma oc_nc_0502: "oc_sub None 502"
  by (oc_eval oc_nc_0502)

lemma oc_nc_0503: "oc_sub None 503"
  by (oc_eval oc_nc_0503)

lemma oc_nc_0504: "oc_sub None 504"
  by (oc_eval oc_nc_0504)

lemma oc_nc_0505: "oc_sub None 505"
  by (oc_eval oc_nc_0505)

lemma oc_nc_0506: "oc_sub None 506"
  by (oc_eval oc_nc_0506)

lemma oc_nc_0507: "oc_sub None 507"
  by (oc_eval oc_nc_0507)

lemma oc_nc_0508: "oc_sub None 508"
  by (oc_eval oc_nc_0508)

lemma oc_nc_0509: "oc_sub None 509"
  by (oc_eval oc_nc_0509)

lemma oc_nc_0510: "oc_sub None 510"
  by (oc_eval oc_nc_0510)

lemma oc_nc_0511: "oc_sub None 511"
  by (oc_eval oc_nc_0511)

lemma upt_nc_031: "[496..<512] = [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]"
  by (simp add: upt_rec)

lemma sec_nc_031: "\<forall>j\<in>{16 * 31..<16 * 31 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 31..<16 * 31 + 16}"
  then have "j \<in> set [496..<512]" unfolding set_upt by simp
  then have "j \<in> set [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]" unfolding upt_nc_031 .
  then show "oc_sub None j" using oc_nc_0496 oc_nc_0497 oc_nc_0498 oc_nc_0499 oc_nc_0500 oc_nc_0501 oc_nc_0502 oc_nc_0503 oc_nc_0504 oc_nc_0505 oc_nc_0506 oc_nc_0507 oc_nc_0508 oc_nc_0509 oc_nc_0510 oc_nc_0511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
