theory OCX_c30_031
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0496: "oc_sub oc_b30 496"
  by (oc_eval oc_c30_0496)

lemma oc_c30_0497: "oc_sub oc_b30 497"
  by (oc_eval oc_c30_0497)

lemma oc_c30_0498: "oc_sub oc_b30 498"
  by (oc_eval oc_c30_0498)

lemma oc_c30_0499: "oc_sub oc_b30 499"
  by (oc_eval oc_c30_0499)

lemma oc_c30_0500: "oc_sub oc_b30 500"
  by (oc_eval oc_c30_0500)

lemma oc_c30_0501: "oc_sub oc_b30 501"
  by (oc_eval oc_c30_0501)

lemma oc_c30_0502: "oc_sub oc_b30 502"
  by (oc_eval oc_c30_0502)

lemma oc_c30_0503: "oc_sub oc_b30 503"
  by (oc_eval oc_c30_0503)

lemma oc_c30_0504: "oc_sub oc_b30 504"
  by (oc_eval oc_c30_0504)

lemma oc_c30_0505: "oc_sub oc_b30 505"
  by (oc_eval oc_c30_0505)

lemma oc_c30_0506: "oc_sub oc_b30 506"
  by (oc_eval oc_c30_0506)

lemma oc_c30_0507: "oc_sub oc_b30 507"
  by (oc_eval oc_c30_0507)

lemma oc_c30_0508: "oc_sub oc_b30 508"
  by (oc_eval oc_c30_0508)

lemma oc_c30_0509: "oc_sub oc_b30 509"
  by (oc_eval oc_c30_0509)

lemma oc_c30_0510: "oc_sub oc_b30 510"
  by (oc_eval oc_c30_0510)

lemma oc_c30_0511: "oc_sub oc_b30 511"
  by (oc_eval oc_c30_0511)

lemma upt_c30_031: "[496..<512] = [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]"
  by (simp add: upt_rec)

lemma sec_c30_031: "\<forall>j\<in>{16 * 31..<16 * 31 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 31..<16 * 31 + 16}"
  then have "j \<in> set [496..<512]" unfolding set_upt by simp
  then have "j \<in> set [496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]" unfolding upt_c30_031 .
  then show "oc_sub oc_b30 j" using oc_c30_0496 oc_c30_0497 oc_c30_0498 oc_c30_0499 oc_c30_0500 oc_c30_0501 oc_c30_0502 oc_c30_0503 oc_c30_0504 oc_c30_0505 oc_c30_0506 oc_c30_0507 oc_c30_0508 oc_c30_0509 oc_c30_0510 oc_c30_0511
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
