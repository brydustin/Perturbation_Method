theory DCX_nc_126
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2016: "dc_sub None 2016"
  by (dc_eval dc_nc_2016)

lemma dc_nc_2017: "dc_sub None 2017"
  by (dc_eval dc_nc_2017)

lemma dc_nc_2018: "dc_sub None 2018"
  by (dc_eval dc_nc_2018)

lemma dc_nc_2019: "dc_sub None 2019"
  by (dc_eval dc_nc_2019)

lemma dc_nc_2020: "dc_sub None 2020"
  by (dc_eval dc_nc_2020)

lemma dc_nc_2021: "dc_sub None 2021"
  by (dc_eval dc_nc_2021)

lemma dc_nc_2022: "dc_sub None 2022"
  by (dc_eval dc_nc_2022)

lemma dc_nc_2023: "dc_sub None 2023"
  by (dc_eval dc_nc_2023)

lemma dc_nc_2024: "dc_sub None 2024"
  by (dc_eval dc_nc_2024)

lemma dc_nc_2025: "dc_sub None 2025"
  by (dc_eval dc_nc_2025)

lemma dc_nc_2026: "dc_sub None 2026"
  by (dc_eval dc_nc_2026)

lemma dc_nc_2027: "dc_sub None 2027"
  by (dc_eval dc_nc_2027)

lemma dc_nc_2028: "dc_sub None 2028"
  by (dc_eval dc_nc_2028)

lemma dc_nc_2029: "dc_sub None 2029"
  by (dc_eval dc_nc_2029)

lemma dc_nc_2030: "dc_sub None 2030"
  by (dc_eval dc_nc_2030)

lemma dc_nc_2031: "dc_sub None 2031"
  by (dc_eval dc_nc_2031)

lemma upt_nc_126: "[2016..<2032] = [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]"
  by (simp add: upt_rec)

lemma sec_nc_126: "\<forall>j\<in>{16 * 126..<16 * 126 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 126..<16 * 126 + 16}"
  then have "j \<in> set [2016..<2032]" unfolding set_upt by simp
  then have "j \<in> set [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]" unfolding upt_nc_126 .
  then show "dc_sub None j" using dc_nc_2016 dc_nc_2017 dc_nc_2018 dc_nc_2019 dc_nc_2020 dc_nc_2021 dc_nc_2022 dc_nc_2023 dc_nc_2024 dc_nc_2025 dc_nc_2026 dc_nc_2027 dc_nc_2028 dc_nc_2029 dc_nc_2030 dc_nc_2031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
