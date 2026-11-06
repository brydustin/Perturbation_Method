theory GOCX_nc_126
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2016: "goc_sub None 2016"
  by (goc_eval goc_nc_2016)

lemma goc_nc_2017: "goc_sub None 2017"
  by (goc_eval goc_nc_2017)

lemma goc_nc_2018: "goc_sub None 2018"
  by (goc_eval goc_nc_2018)

lemma goc_nc_2019: "goc_sub None 2019"
  by (goc_eval goc_nc_2019)

lemma goc_nc_2020: "goc_sub None 2020"
  by (goc_eval goc_nc_2020)

lemma goc_nc_2021: "goc_sub None 2021"
  by (goc_eval goc_nc_2021)

lemma goc_nc_2022: "goc_sub None 2022"
  by (goc_eval goc_nc_2022)

lemma goc_nc_2023: "goc_sub None 2023"
  by (goc_eval goc_nc_2023)

lemma goc_nc_2024: "goc_sub None 2024"
  by (goc_eval goc_nc_2024)

lemma goc_nc_2025: "goc_sub None 2025"
  by (goc_eval goc_nc_2025)

lemma goc_nc_2026: "goc_sub None 2026"
  by (goc_eval goc_nc_2026)

lemma goc_nc_2027: "goc_sub None 2027"
  by (goc_eval goc_nc_2027)

lemma goc_nc_2028: "goc_sub None 2028"
  by (goc_eval goc_nc_2028)

lemma goc_nc_2029: "goc_sub None 2029"
  by (goc_eval goc_nc_2029)

lemma goc_nc_2030: "goc_sub None 2030"
  by (goc_eval goc_nc_2030)

lemma goc_nc_2031: "goc_sub None 2031"
  by (goc_eval goc_nc_2031)

lemma gupt_nc_126: "[2016..<2032] = [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]"
  by (simp add: upt_rec)

lemma gsec_nc_126: "\<forall>j\<in>{16 * 126..<16 * 126 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 126..<16 * 126 + 16}"
  then have "j \<in> set [2016..<2032]" unfolding set_upt by simp
  then have "j \<in> set [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]" unfolding gupt_nc_126 .
  then show "goc_sub None j" using goc_nc_2016 goc_nc_2017 goc_nc_2018 goc_nc_2019 goc_nc_2020 goc_nc_2021 goc_nc_2022 goc_nc_2023 goc_nc_2024 goc_nc_2025 goc_nc_2026 goc_nc_2027 goc_nc_2028 goc_nc_2029 goc_nc_2030 goc_nc_2031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
