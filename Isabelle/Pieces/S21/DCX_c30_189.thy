theory DCX_c30_189
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3024: "dc_sub dc_b30 3024"
  by (dc_eval dc_c30_3024)

lemma dc_c30_3025: "dc_sub dc_b30 3025"
  by (dc_eval dc_c30_3025)

lemma dc_c30_3026: "dc_sub dc_b30 3026"
  by (dc_eval dc_c30_3026)

lemma dc_c30_3027: "dc_sub dc_b30 3027"
  by (dc_eval dc_c30_3027)

lemma dc_c30_3028: "dc_sub dc_b30 3028"
  by (dc_eval dc_c30_3028)

lemma dc_c30_3029: "dc_sub dc_b30 3029"
  by (dc_eval dc_c30_3029)

lemma dc_c30_3030: "dc_sub dc_b30 3030"
  by (dc_eval dc_c30_3030)

lemma dc_c30_3031: "dc_sub dc_b30 3031"
  by (dc_eval dc_c30_3031)

lemma dc_c30_3032: "dc_sub dc_b30 3032"
  by (dc_eval dc_c30_3032)

lemma dc_c30_3033: "dc_sub dc_b30 3033"
  by (dc_eval dc_c30_3033)

lemma dc_c30_3034: "dc_sub dc_b30 3034"
  by (dc_eval dc_c30_3034)

lemma dc_c30_3035: "dc_sub dc_b30 3035"
  by (dc_eval dc_c30_3035)

lemma dc_c30_3036: "dc_sub dc_b30 3036"
  by (dc_eval dc_c30_3036)

lemma dc_c30_3037: "dc_sub dc_b30 3037"
  by (dc_eval dc_c30_3037)

lemma dc_c30_3038: "dc_sub dc_b30 3038"
  by (dc_eval dc_c30_3038)

lemma dc_c30_3039: "dc_sub dc_b30 3039"
  by (dc_eval dc_c30_3039)

lemma upt_c30_189: "[3024..<3040] = [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]"
  by (simp add: upt_rec)

lemma sec_c30_189: "\<forall>j\<in>{16 * 189..<16 * 189 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 189..<16 * 189 + 16}"
  then have "j \<in> set [3024..<3040]" unfolding set_upt by simp
  then have "j \<in> set [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]" unfolding upt_c30_189 .
  then show "dc_sub dc_b30 j" using dc_c30_3024 dc_c30_3025 dc_c30_3026 dc_c30_3027 dc_c30_3028 dc_c30_3029 dc_c30_3030 dc_c30_3031 dc_c30_3032 dc_c30_3033 dc_c30_3034 dc_c30_3035 dc_c30_3036 dc_c30_3037 dc_c30_3038 dc_c30_3039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
