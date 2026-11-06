theory OCX_c30_126
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2016: "oc_sub oc_b30 2016"
  by (oc_eval oc_c30_2016)

lemma oc_c30_2017: "oc_sub oc_b30 2017"
  by (oc_eval oc_c30_2017)

lemma oc_c30_2018: "oc_sub oc_b30 2018"
  by (oc_eval oc_c30_2018)

lemma oc_c30_2019: "oc_sub oc_b30 2019"
  by (oc_eval oc_c30_2019)

lemma oc_c30_2020: "oc_sub oc_b30 2020"
  by (oc_eval oc_c30_2020)

lemma oc_c30_2021: "oc_sub oc_b30 2021"
  by (oc_eval oc_c30_2021)

lemma oc_c30_2022: "oc_sub oc_b30 2022"
  by (oc_eval oc_c30_2022)

lemma oc_c30_2023: "oc_sub oc_b30 2023"
  by (oc_eval oc_c30_2023)

lemma oc_c30_2024: "oc_sub oc_b30 2024"
  by (oc_eval oc_c30_2024)

lemma oc_c30_2025: "oc_sub oc_b30 2025"
  by (oc_eval oc_c30_2025)

lemma oc_c30_2026: "oc_sub oc_b30 2026"
  by (oc_eval oc_c30_2026)

lemma oc_c30_2027: "oc_sub oc_b30 2027"
  by (oc_eval oc_c30_2027)

lemma oc_c30_2028: "oc_sub oc_b30 2028"
  by (oc_eval oc_c30_2028)

lemma oc_c30_2029: "oc_sub oc_b30 2029"
  by (oc_eval oc_c30_2029)

lemma oc_c30_2030: "oc_sub oc_b30 2030"
  by (oc_eval oc_c30_2030)

lemma oc_c30_2031: "oc_sub oc_b30 2031"
  by (oc_eval oc_c30_2031)

lemma upt_c30_126: "[2016..<2032] = [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]"
  by (simp add: upt_rec)

lemma sec_c30_126: "\<forall>j\<in>{16 * 126..<16 * 126 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 126..<16 * 126 + 16}"
  then have "j \<in> set [2016..<2032]" unfolding set_upt by simp
  then have "j \<in> set [2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031]" unfolding upt_c30_126 .
  then show "oc_sub oc_b30 j" using oc_c30_2016 oc_c30_2017 oc_c30_2018 oc_c30_2019 oc_c30_2020 oc_c30_2021 oc_c30_2022 oc_c30_2023 oc_c30_2024 oc_c30_2025 oc_c30_2026 oc_c30_2027 oc_c30_2028 oc_c30_2029 oc_c30_2030 oc_c30_2031
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
