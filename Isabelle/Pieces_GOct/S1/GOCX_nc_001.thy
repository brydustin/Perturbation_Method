theory GOCX_nc_001
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0016: "goc_sub None 16"
  by (goc_eval goc_nc_0016)

lemma goc_nc_0017: "goc_sub None 17"
  by (goc_eval goc_nc_0017)

lemma goc_nc_0018: "goc_sub None 18"
  by (goc_eval goc_nc_0018)

lemma goc_nc_0019: "goc_sub None 19"
  by (goc_eval goc_nc_0019)

lemma goc_nc_0020: "goc_sub None 20"
  by (goc_eval goc_nc_0020)

lemma goc_nc_0021: "goc_sub None 21"
  by (goc_eval goc_nc_0021)

lemma goc_nc_0022: "goc_sub None 22"
  by (goc_eval goc_nc_0022)

lemma goc_nc_0023: "goc_sub None 23"
  by (goc_eval goc_nc_0023)

lemma goc_nc_0024: "goc_sub None 24"
  by (goc_eval goc_nc_0024)

lemma goc_nc_0025: "goc_sub None 25"
  by (goc_eval goc_nc_0025)

lemma goc_nc_0026: "goc_sub None 26"
  by (goc_eval goc_nc_0026)

lemma goc_nc_0027: "goc_sub None 27"
  by (goc_eval goc_nc_0027)

lemma goc_nc_0028: "goc_sub None 28"
  by (goc_eval goc_nc_0028)

lemma goc_nc_0029: "goc_sub None 29"
  by (goc_eval goc_nc_0029)

lemma goc_nc_0030: "goc_sub None 30"
  by (goc_eval goc_nc_0030)

lemma goc_nc_0031: "goc_sub None 31"
  by (goc_eval goc_nc_0031)

lemma gupt_nc_001: "[16..<32] = [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]"
  by (simp add: upt_rec)

lemma gsec_nc_001: "\<forall>j\<in>{16 * 1..<16 * 1 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 1..<16 * 1 + 16}"
  then have "j \<in> set [16..<32]" unfolding set_upt by simp
  then have "j \<in> set [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]" unfolding gupt_nc_001 .
  then show "goc_sub None j" using goc_nc_0016 goc_nc_0017 goc_nc_0018 goc_nc_0019 goc_nc_0020 goc_nc_0021 goc_nc_0022 goc_nc_0023 goc_nc_0024 goc_nc_0025 goc_nc_0026 goc_nc_0027 goc_nc_0028 goc_nc_0029 goc_nc_0030 goc_nc_0031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
