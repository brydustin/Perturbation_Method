theory GDCX_nc_126
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2016: "gdc_sub None 2016"
  by (gdc_eval gdc_nc_2016)

lemma gdc_nc_2017: "gdc_sub None 2017"
  by (gdc_eval gdc_nc_2017)

lemma gdc_nc_2018: "gdc_sub None 2018"
  by (gdc_eval gdc_nc_2018)

lemma gdc_nc_2019: "gdc_sub None 2019"
  by (gdc_eval gdc_nc_2019)

lemma gdc_nc_2020: "gdc_sub None 2020"
  by (gdc_eval gdc_nc_2020)

lemma gdc_nc_2021: "gdc_sub None 2021"
  by (gdc_eval gdc_nc_2021)

lemma gdc_nc_2022: "gdc_sub None 2022"
  by (gdc_eval gdc_nc_2022)

lemma gdc_nc_2023: "gdc_sub None 2023"
  by (gdc_eval gdc_nc_2023)

lemma gdc_nc_2024: "gdc_sub None 2024"
  by (gdc_eval gdc_nc_2024)

lemma gdc_nc_2025: "gdc_sub None 2025"
  by (gdc_eval gdc_nc_2025)

lemma gdc_nc_2026: "gdc_sub None 2026"
  by (gdc_eval gdc_nc_2026)

lemma gdc_nc_2027: "gdc_sub None 2027"
  by (gdc_eval gdc_nc_2027)

lemma gdc_nc_2028: "gdc_sub None 2028"
  by (gdc_eval gdc_nc_2028)

lemma gdc_nc_2029: "gdc_sub None 2029"
  by (gdc_eval gdc_nc_2029)

lemma gdc_nc_2030: "gdc_sub None 2030"
  by (gdc_eval gdc_nc_2030)

lemma gdc_nc_2031: "gdc_sub None 2031"
  by (gdc_eval gdc_nc_2031)

lemma gupt_nc_126: "[2016..<2032] = [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]"
  by (simp add: upt_rec)

lemma gsec_nc_126: "\<forall>j\<in>{16 * 126..<16 * 126 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 126..<16 * 126 + 16}"
  then have "j \<in> set [2016..<2032]" unfolding set_upt by simp
  then have "j \<in> set [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]" unfolding gupt_nc_126 .
  then show "gdc_sub None j" using gdc_nc_2016 gdc_nc_2017 gdc_nc_2018 gdc_nc_2019 gdc_nc_2020 gdc_nc_2021 gdc_nc_2022 gdc_nc_2023 gdc_nc_2024 gdc_nc_2025 gdc_nc_2026 gdc_nc_2027 gdc_nc_2028 gdc_nc_2029 gdc_nc_2030 gdc_nc_2031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
