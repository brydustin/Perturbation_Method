theory DCX_c30_001
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0016: "dc_sub dc_b30 16"
  by (dc_eval dc_c30_0016)

lemma dc_c30_0017: "dc_sub dc_b30 17"
  by (dc_eval dc_c30_0017)

lemma dc_c30_0018: "dc_sub dc_b30 18"
  by (dc_eval dc_c30_0018)

lemma dc_c30_0019: "dc_sub dc_b30 19"
  by (dc_eval dc_c30_0019)

lemma dc_c30_0020: "dc_sub dc_b30 20"
  by (dc_eval dc_c30_0020)

lemma dc_c30_0021: "dc_sub dc_b30 21"
  by (dc_eval dc_c30_0021)

lemma dc_c30_0022: "dc_sub dc_b30 22"
  by (dc_eval dc_c30_0022)

lemma dc_c30_0023: "dc_sub dc_b30 23"
  by (dc_eval dc_c30_0023)

lemma dc_c30_0024: "dc_sub dc_b30 24"
  by (dc_eval dc_c30_0024)

lemma dc_c30_0025: "dc_sub dc_b30 25"
  by (dc_eval dc_c30_0025)

lemma dc_c30_0026: "dc_sub dc_b30 26"
  by (dc_eval dc_c30_0026)

lemma dc_c30_0027: "dc_sub dc_b30 27"
  by (dc_eval dc_c30_0027)

lemma dc_c30_0028: "dc_sub dc_b30 28"
  by (dc_eval dc_c30_0028)

lemma dc_c30_0029: "dc_sub dc_b30 29"
  by (dc_eval dc_c30_0029)

lemma dc_c30_0030: "dc_sub dc_b30 30"
  by (dc_eval dc_c30_0030)

lemma dc_c30_0031: "dc_sub dc_b30 31"
  by (dc_eval dc_c30_0031)

lemma upt_c30_001: "[16..<32] = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]"
  by (simp add: upt_rec)

lemma sec_c30_001: "\<forall>j\<in>{16 * 1..<16 * 1 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 1..<16 * 1 + 16}"
  then have "j \<in> set [16..<32]" unfolding set_upt by simp
  then have "j \<in> set [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]" unfolding upt_c30_001 .
  then show "dc_sub dc_b30 j" using dc_c30_0016 dc_c30_0017 dc_c30_0018 dc_c30_0019 dc_c30_0020 dc_c30_0021 dc_c30_0022 dc_c30_0023 dc_c30_0024 dc_c30_0025 dc_c30_0026 dc_c30_0027 dc_c30_0028 dc_c30_0029 dc_c30_0030 dc_c30_0031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
