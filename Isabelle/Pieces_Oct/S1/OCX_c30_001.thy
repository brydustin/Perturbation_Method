theory OCX_c30_001
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0016: "oc_sub oc_b30 16"
  by (oc_eval oc_c30_0016)

lemma oc_c30_0017: "oc_sub oc_b30 17"
  by (oc_eval oc_c30_0017)

lemma oc_c30_0018: "oc_sub oc_b30 18"
  by (oc_eval oc_c30_0018)

lemma oc_c30_0019: "oc_sub oc_b30 19"
  by (oc_eval oc_c30_0019)

lemma oc_c30_0020: "oc_sub oc_b30 20"
  by (oc_eval oc_c30_0020)

lemma oc_c30_0021: "oc_sub oc_b30 21"
  by (oc_eval oc_c30_0021)

lemma oc_c30_0022: "oc_sub oc_b30 22"
  by (oc_eval oc_c30_0022)

lemma oc_c30_0023: "oc_sub oc_b30 23"
  by (oc_eval oc_c30_0023)

lemma oc_c30_0024: "oc_sub oc_b30 24"
  by (oc_eval oc_c30_0024)

lemma oc_c30_0025: "oc_sub oc_b30 25"
  by (oc_eval oc_c30_0025)

lemma oc_c30_0026: "oc_sub oc_b30 26"
  by (oc_eval oc_c30_0026)

lemma oc_c30_0027: "oc_sub oc_b30 27"
  by (oc_eval oc_c30_0027)

lemma oc_c30_0028: "oc_sub oc_b30 28"
  by (oc_eval oc_c30_0028)

lemma oc_c30_0029: "oc_sub oc_b30 29"
  by (oc_eval oc_c30_0029)

lemma oc_c30_0030: "oc_sub oc_b30 30"
  by (oc_eval oc_c30_0030)

lemma oc_c30_0031: "oc_sub oc_b30 31"
  by (oc_eval oc_c30_0031)

lemma upt_c30_001: "[16..<32] = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]"
  by (simp add: upt_rec)

lemma sec_c30_001: "\<forall>j\<in>{16 * 1..<16 * 1 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 1..<16 * 1 + 16}"
  then have "j \<in> set [16..<32]" unfolding set_upt by simp
  then have "j \<in> set [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]" unfolding upt_c30_001 .
  then show "oc_sub oc_b30 j" using oc_c30_0016 oc_c30_0017 oc_c30_0018 oc_c30_0019 oc_c30_0020 oc_c30_0021 oc_c30_0022 oc_c30_0023 oc_c30_0024 oc_c30_0025 oc_c30_0026 oc_c30_0027 oc_c30_0028 oc_c30_0029 oc_c30_0030 oc_c30_0031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
