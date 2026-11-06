theory GDCX_nc_001
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0016: "gdc_sub None 16"
  by (gdc_eval gdc_nc_0016)

lemma gdc_nc_0017: "gdc_sub None 17"
  by (gdc_eval gdc_nc_0017)

lemma gdc_nc_0018: "gdc_sub None 18"
  by (gdc_eval gdc_nc_0018)

lemma gdc_nc_0019: "gdc_sub None 19"
  by (gdc_eval gdc_nc_0019)

lemma gdc_nc_0020: "gdc_sub None 20"
  by (gdc_eval gdc_nc_0020)

lemma gdc_nc_0021: "gdc_sub None 21"
  by (gdc_eval gdc_nc_0021)

lemma gdc_nc_0022: "gdc_sub None 22"
  by (gdc_eval gdc_nc_0022)

lemma gdc_nc_0023: "gdc_sub None 23"
  by (gdc_eval gdc_nc_0023)

lemma gdc_nc_0024: "gdc_sub None 24"
  by (gdc_eval gdc_nc_0024)

lemma gdc_nc_0025: "gdc_sub None 25"
  by (gdc_eval gdc_nc_0025)

lemma gdc_nc_0026: "gdc_sub None 26"
  by (gdc_eval gdc_nc_0026)

lemma gdc_nc_0027: "gdc_sub None 27"
  by (gdc_eval gdc_nc_0027)

lemma gdc_nc_0028: "gdc_sub None 28"
  by (gdc_eval gdc_nc_0028)

lemma gdc_nc_0029: "gdc_sub None 29"
  by (gdc_eval gdc_nc_0029)

lemma gdc_nc_0030: "gdc_sub None 30"
  by (gdc_eval gdc_nc_0030)

lemma gdc_nc_0031: "gdc_sub None 31"
  by (gdc_eval gdc_nc_0031)

lemma gupt_nc_001: "[16..<32] = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]"
  by (simp add: upt_rec)

lemma gsec_nc_001: "\<forall>j\<in>{16 * 1..<16 * 1 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 1..<16 * 1 + 16}"
  then have "j \<in> set [16..<32]" unfolding set_upt by simp
  then have "j \<in> set [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]" unfolding gupt_nc_001 .
  then show "gdc_sub None j" using gdc_nc_0016 gdc_nc_0017 gdc_nc_0018 gdc_nc_0019 gdc_nc_0020 gdc_nc_0021 gdc_nc_0022 gdc_nc_0023 gdc_nc_0024 gdc_nc_0025 gdc_nc_0026 gdc_nc_0027 gdc_nc_0028 gdc_nc_0029 gdc_nc_0030 gdc_nc_0031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
