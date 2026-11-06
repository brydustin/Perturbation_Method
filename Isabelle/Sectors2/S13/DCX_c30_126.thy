theory DCX_c30_126
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2016: "dc_sub dc_b30 2016"
  by (dc_eval dc_c30_2016)

lemma dc_c30_2017: "dc_sub dc_b30 2017"
  by (dc_eval dc_c30_2017)

lemma dc_c30_2018: "dc_sub dc_b30 2018"
  by (dc_eval dc_c30_2018)

lemma dc_c30_2019: "dc_sub dc_b30 2019"
  by (dc_eval dc_c30_2019)

lemma dc_c30_2020: "dc_sub dc_b30 2020"
  by (dc_eval dc_c30_2020)

lemma dc_c30_2021: "dc_sub dc_b30 2021"
  by (dc_eval dc_c30_2021)

lemma dc_c30_2022: "dc_sub dc_b30 2022"
  by (dc_eval dc_c30_2022)

lemma dc_c30_2023: "dc_sub dc_b30 2023"
  by (dc_eval dc_c30_2023)

lemma dc_c30_2024: "dc_sub dc_b30 2024"
  by (dc_eval dc_c30_2024)

lemma dc_c30_2025: "dc_sub dc_b30 2025"
  by (dc_eval dc_c30_2025)

lemma dc_c30_2026: "dc_sub dc_b30 2026"
  by (dc_eval dc_c30_2026)

lemma dc_c30_2027: "dc_sub dc_b30 2027"
  by (dc_eval dc_c30_2027)

lemma dc_c30_2028: "dc_sub dc_b30 2028"
  by (dc_eval dc_c30_2028)

lemma dc_c30_2029: "dc_sub dc_b30 2029"
  by (dc_eval dc_c30_2029)

lemma dc_c30_2030: "dc_sub dc_b30 2030"
  by (dc_eval dc_c30_2030)

lemma dc_c30_2031: "dc_sub dc_b30 2031"
  by (dc_eval dc_c30_2031)

lemma upt_c30_126: "[2016..<2032] = [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]"
  by (simp add: upt_rec)

lemma sec_c30_126: "\<forall>j\<in>{16 * 126..<16 * 126 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 126..<16 * 126 + 16}"
  then have "j \<in> set [2016..<2032]" unfolding set_upt by simp
  then have "j \<in> set [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]" unfolding upt_c30_126 .
  then show "dc_sub dc_b30 j" using dc_c30_2016 dc_c30_2017 dc_c30_2018 dc_c30_2019 dc_c30_2020 dc_c30_2021 dc_c30_2022 dc_c30_2023 dc_c30_2024 dc_c30_2025 dc_c30_2026 dc_c30_2027 dc_c30_2028 dc_c30_2029 dc_c30_2030 dc_c30_2031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
