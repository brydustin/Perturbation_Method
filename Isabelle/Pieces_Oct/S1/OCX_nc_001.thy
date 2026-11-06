theory OCX_nc_001
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0016: "oc_sub None 16"
  by (oc_eval oc_nc_0016)

lemma oc_nc_0017: "oc_sub None 17"
  by (oc_eval oc_nc_0017)

lemma oc_nc_0018: "oc_sub None 18"
  by (oc_eval oc_nc_0018)

lemma oc_nc_0019: "oc_sub None 19"
  by (oc_eval oc_nc_0019)

lemma oc_nc_0020: "oc_sub None 20"
  by (oc_eval oc_nc_0020)

lemma oc_nc_0021: "oc_sub None 21"
  by (oc_eval oc_nc_0021)

lemma oc_nc_0022: "oc_sub None 22"
  by (oc_eval oc_nc_0022)

lemma oc_nc_0023: "oc_sub None 23"
  by (oc_eval oc_nc_0023)

lemma oc_nc_0024: "oc_sub None 24"
  by (oc_eval oc_nc_0024)

lemma oc_nc_0025: "oc_sub None 25"
  by (oc_eval oc_nc_0025)

lemma oc_nc_0026: "oc_sub None 26"
  by (oc_eval oc_nc_0026)

lemma oc_nc_0027: "oc_sub None 27"
  by (oc_eval oc_nc_0027)

lemma oc_nc_0028: "oc_sub None 28"
  by (oc_eval oc_nc_0028)

lemma oc_nc_0029: "oc_sub None 29"
  by (oc_eval oc_nc_0029)

lemma oc_nc_0030: "oc_sub None 30"
  by (oc_eval oc_nc_0030)

lemma oc_nc_0031: "oc_sub None 31"
  by (oc_eval oc_nc_0031)

lemma upt_nc_001: "[16..<32] = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]"
  by (simp add: upt_rec)

lemma sec_nc_001: "\<forall>j\<in>{16 * 1..<16 * 1 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 1..<16 * 1 + 16}"
  then have "j \<in> set [16..<32]" unfolding set_upt by simp
  then have "j \<in> set [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]" unfolding upt_nc_001 .
  then show "oc_sub None j" using oc_nc_0016 oc_nc_0017 oc_nc_0018 oc_nc_0019 oc_nc_0020 oc_nc_0021 oc_nc_0022 oc_nc_0023 oc_nc_0024 oc_nc_0025 oc_nc_0026 oc_nc_0027 oc_nc_0028 oc_nc_0029 oc_nc_0030 oc_nc_0031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
