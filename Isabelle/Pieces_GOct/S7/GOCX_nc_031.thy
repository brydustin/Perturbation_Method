theory GOCX_nc_031
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0496: "goc_sub None 496"
  by (goc_eval goc_nc_0496)

lemma goc_nc_0497: "goc_sub None 497"
  by (goc_eval goc_nc_0497)

lemma goc_nc_0498: "goc_sub None 498"
  by (goc_eval goc_nc_0498)

lemma goc_nc_0499: "goc_sub None 499"
  by (goc_eval goc_nc_0499)

lemma goc_nc_0500: "goc_sub None 500"
  by (goc_eval goc_nc_0500)

lemma goc_nc_0501: "goc_sub None 501"
  by (goc_eval goc_nc_0501)

lemma goc_nc_0502: "goc_sub None 502"
  by (goc_eval goc_nc_0502)

lemma goc_nc_0503: "goc_sub None 503"
  by (goc_eval goc_nc_0503)

lemma goc_nc_0504: "goc_sub None 504"
  by (goc_eval goc_nc_0504)

lemma goc_nc_0505: "goc_sub None 505"
  by (goc_eval goc_nc_0505)

lemma goc_nc_0506: "goc_sub None 506"
  by (goc_eval goc_nc_0506)

lemma goc_nc_0507: "goc_sub None 507"
  by (goc_eval goc_nc_0507)

lemma goc_nc_0508: "goc_sub None 508"
  by (goc_eval goc_nc_0508)

lemma goc_nc_0509: "goc_sub None 509"
  by (goc_eval goc_nc_0509)

lemma goc_nc_0510: "goc_sub None 510"
  by (goc_eval goc_nc_0510)

lemma goc_nc_0511: "goc_sub None 511"
  by (goc_eval goc_nc_0511)

lemma gupt_nc_031: "[496..<512] = [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]"
  by (simp add: upt_rec)

lemma gsec_nc_031: "\<forall>j\<in>{16 * 31..<16 * 31 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 31..<16 * 31 + 16}"
  then have "j \<in> set [496..<512]" unfolding set_upt by simp
  then have "j \<in> set [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]" unfolding gupt_nc_031 .
  then show "goc_sub None j" using goc_nc_0496 goc_nc_0497 goc_nc_0498 goc_nc_0499 goc_nc_0500 goc_nc_0501 goc_nc_0502 goc_nc_0503 goc_nc_0504 goc_nc_0505 goc_nc_0506 goc_nc_0507 goc_nc_0508 goc_nc_0509 goc_nc_0510 goc_nc_0511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
