theory DCX_nc_001
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0016: "dc_sub None 16"
  by (dc_eval dc_nc_0016)

lemma dc_nc_0017: "dc_sub None 17"
  by (dc_eval dc_nc_0017)

lemma dc_nc_0018: "dc_sub None 18"
  by (dc_eval dc_nc_0018)

lemma dc_nc_0019: "dc_sub None 19"
  by (dc_eval dc_nc_0019)

lemma dc_nc_0020: "dc_sub None 20"
  by (dc_eval dc_nc_0020)

lemma dc_nc_0021: "dc_sub None 21"
  by (dc_eval dc_nc_0021)

lemma dc_nc_0022: "dc_sub None 22"
  by (dc_eval dc_nc_0022)

lemma dc_nc_0023: "dc_sub None 23"
  by (dc_eval dc_nc_0023)

lemma dc_nc_0024: "dc_sub None 24"
  by (dc_eval dc_nc_0024)

lemma dc_nc_0025: "dc_sub None 25"
  by (dc_eval dc_nc_0025)

lemma dc_nc_0026: "dc_sub None 26"
  by (dc_eval dc_nc_0026)

lemma dc_nc_0027: "dc_sub None 27"
  by (dc_eval dc_nc_0027)

lemma dc_nc_0028: "dc_sub None 28"
  by (dc_eval dc_nc_0028)

lemma dc_nc_0029: "dc_sub None 29"
  by (dc_eval dc_nc_0029)

lemma dc_nc_0030: "dc_sub None 30"
  by (dc_eval dc_nc_0030)

lemma dc_nc_0031: "dc_sub None 31"
  by (dc_eval dc_nc_0031)

lemma upt_nc_001: "[16..<32] = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]"
  by (simp add: upt_rec)

lemma sec_nc_001: "\<forall>j\<in>{16 * 1..<16 * 1 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 1..<16 * 1 + 16}"
  then have "j \<in> set [16..<32]" unfolding set_upt by simp
  then have "j \<in> set [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]" unfolding upt_nc_001 .
  then show "dc_sub None j" using dc_nc_0016 dc_nc_0017 dc_nc_0018 dc_nc_0019 dc_nc_0020 dc_nc_0021 dc_nc_0022 dc_nc_0023 dc_nc_0024 dc_nc_0025 dc_nc_0026 dc_nc_0027 dc_nc_0028 dc_nc_0029 dc_nc_0030 dc_nc_0031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
