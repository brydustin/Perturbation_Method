theory OCX_nc_126
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2016: "oc_sub None 2016"
  by (oc_eval oc_nc_2016)

lemma oc_nc_2017: "oc_sub None 2017"
  by (oc_eval oc_nc_2017)

lemma oc_nc_2018: "oc_sub None 2018"
  by (oc_eval oc_nc_2018)

lemma oc_nc_2019: "oc_sub None 2019"
  by (oc_eval oc_nc_2019)

lemma oc_nc_2020: "oc_sub None 2020"
  by (oc_eval oc_nc_2020)

lemma oc_nc_2021: "oc_sub None 2021"
  by (oc_eval oc_nc_2021)

lemma oc_nc_2022: "oc_sub None 2022"
  by (oc_eval oc_nc_2022)

lemma oc_nc_2023: "oc_sub None 2023"
  by (oc_eval oc_nc_2023)

lemma oc_nc_2024: "oc_sub None 2024"
  by (oc_eval oc_nc_2024)

lemma oc_nc_2025: "oc_sub None 2025"
  by (oc_eval oc_nc_2025)

lemma oc_nc_2026: "oc_sub None 2026"
  by (oc_eval oc_nc_2026)

lemma oc_nc_2027: "oc_sub None 2027"
  by (oc_eval oc_nc_2027)

lemma oc_nc_2028: "oc_sub None 2028"
  by (oc_eval oc_nc_2028)

lemma oc_nc_2029: "oc_sub None 2029"
  by (oc_eval oc_nc_2029)

lemma oc_nc_2030: "oc_sub None 2030"
  by (oc_eval oc_nc_2030)

lemma oc_nc_2031: "oc_sub None 2031"
  by (oc_eval oc_nc_2031)

lemma upt_nc_126: "[2016..<2032] = [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]"
  by (simp add: upt_rec)

lemma sec_nc_126: "\<forall>j\<in>{16 * 126..<16 * 126 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 126..<16 * 126 + 16}"
  then have "j \<in> set [2016..<2032]" unfolding set_upt by simp
  then have "j \<in> set [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]" unfolding upt_nc_126 .
  then show "oc_sub None j" using oc_nc_2016 oc_nc_2017 oc_nc_2018 oc_nc_2019 oc_nc_2020 oc_nc_2021 oc_nc_2022 oc_nc_2023 oc_nc_2024 oc_nc_2025 oc_nc_2026 oc_nc_2027 oc_nc_2028 oc_nc_2029 oc_nc_2030 oc_nc_2031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
