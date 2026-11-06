theory DCX_nc_189
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3024: "dc_sub None 3024"
  by (dc_eval dc_nc_3024)

lemma dc_nc_3025: "dc_sub None 3025"
  by (dc_eval dc_nc_3025)

lemma dc_nc_3026: "dc_sub None 3026"
  by (dc_eval dc_nc_3026)

lemma dc_nc_3027: "dc_sub None 3027"
  by (dc_eval dc_nc_3027)

lemma dc_nc_3028: "dc_sub None 3028"
  by (dc_eval dc_nc_3028)

lemma dc_nc_3029: "dc_sub None 3029"
  by (dc_eval dc_nc_3029)

lemma dc_nc_3030: "dc_sub None 3030"
  by (dc_eval dc_nc_3030)

lemma dc_nc_3031: "dc_sub None 3031"
  by (dc_eval dc_nc_3031)

lemma dc_nc_3032: "dc_sub None 3032"
  by (dc_eval dc_nc_3032)

lemma dc_nc_3033: "dc_sub None 3033"
  by (dc_eval dc_nc_3033)

lemma dc_nc_3034: "dc_sub None 3034"
  by (dc_eval dc_nc_3034)

lemma dc_nc_3035: "dc_sub None 3035"
  by (dc_eval dc_nc_3035)

lemma dc_nc_3036: "dc_sub None 3036"
  by (dc_eval dc_nc_3036)

lemma dc_nc_3037: "dc_sub None 3037"
  by (dc_eval dc_nc_3037)

lemma dc_nc_3038: "dc_sub None 3038"
  by (dc_eval dc_nc_3038)

lemma dc_nc_3039: "dc_sub None 3039"
  by (dc_eval dc_nc_3039)

lemma upt_nc_189: "[3024..<3040] = [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]"
  by (simp add: upt_rec)

lemma sec_nc_189: "\<forall>j\<in>{16 * 189..<16 * 189 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 189..<16 * 189 + 16}"
  then have "j \<in> set [3024..<3040]" unfolding set_upt by simp
  then have "j \<in> set [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]" unfolding upt_nc_189 .
  then show "dc_sub None j" using dc_nc_3024 dc_nc_3025 dc_nc_3026 dc_nc_3027 dc_nc_3028 dc_nc_3029 dc_nc_3030 dc_nc_3031 dc_nc_3032 dc_nc_3033 dc_nc_3034 dc_nc_3035 dc_nc_3036 dc_nc_3037 dc_nc_3038 dc_nc_3039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
