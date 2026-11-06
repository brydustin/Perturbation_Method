theory GDCX_nc_031
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0496: "gdc_sub None 496"
  by (gdc_eval gdc_nc_0496)

lemma gdc_nc_0497: "gdc_sub None 497"
  by (gdc_eval gdc_nc_0497)

lemma gdc_nc_0498: "gdc_sub None 498"
  by (gdc_eval gdc_nc_0498)

lemma gdc_nc_0499: "gdc_sub None 499"
  by (gdc_eval gdc_nc_0499)

lemma gdc_nc_0500: "gdc_sub None 500"
  by (gdc_eval gdc_nc_0500)

lemma gdc_nc_0501: "gdc_sub None 501"
  by (gdc_eval gdc_nc_0501)

lemma gdc_nc_0502: "gdc_sub None 502"
  by (gdc_eval gdc_nc_0502)

lemma gdc_nc_0503: "gdc_sub None 503"
  by (gdc_eval gdc_nc_0503)

lemma gdc_nc_0504: "gdc_sub None 504"
  by (gdc_eval gdc_nc_0504)

lemma gdc_nc_0505: "gdc_sub None 505"
  by (gdc_eval gdc_nc_0505)

lemma gdc_nc_0506: "gdc_sub None 506"
  by (gdc_eval gdc_nc_0506)

lemma gdc_nc_0507: "gdc_sub None 507"
  by (gdc_eval gdc_nc_0507)

lemma gdc_nc_0508: "gdc_sub None 508"
  by (gdc_eval gdc_nc_0508)

lemma gdc_nc_0509: "gdc_sub None 509"
  by (gdc_eval gdc_nc_0509)

lemma gdc_nc_0510: "gdc_sub None 510"
  by (gdc_eval gdc_nc_0510)

lemma gdc_nc_0511: "gdc_sub None 511"
  by (gdc_eval gdc_nc_0511)

lemma gupt_nc_031: "[496..<512] = [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]"
  by (simp add: upt_rec)

lemma gsec_nc_031: "\<forall>j\<in>{16 * 31..<16 * 31 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 31..<16 * 31 + 16}"
  then have "j \<in> set [496..<512]" unfolding set_upt by simp
  then have "j \<in> set [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]" unfolding gupt_nc_031 .
  then show "gdc_sub None j" using gdc_nc_0496 gdc_nc_0497 gdc_nc_0498 gdc_nc_0499 gdc_nc_0500 gdc_nc_0501 gdc_nc_0502 gdc_nc_0503 gdc_nc_0504 gdc_nc_0505 gdc_nc_0506 gdc_nc_0507 gdc_nc_0508 gdc_nc_0509 gdc_nc_0510 gdc_nc_0511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
