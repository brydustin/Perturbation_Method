theory OCX_nc_189
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3024: "oc_sub None 3024"
  by (oc_eval oc_nc_3024)

lemma oc_nc_3025: "oc_sub None 3025"
  by (oc_eval oc_nc_3025)

lemma oc_nc_3026: "oc_sub None 3026"
  by (oc_eval oc_nc_3026)

lemma oc_nc_3027: "oc_sub None 3027"
  by (oc_eval oc_nc_3027)

lemma oc_nc_3028: "oc_sub None 3028"
  by (oc_eval oc_nc_3028)

lemma oc_nc_3029: "oc_sub None 3029"
  by (oc_eval oc_nc_3029)

lemma oc_nc_3030: "oc_sub None 3030"
  by (oc_eval oc_nc_3030)

lemma oc_nc_3031: "oc_sub None 3031"
  by (oc_eval oc_nc_3031)

lemma oc_nc_3032: "oc_sub None 3032"
  by (oc_eval oc_nc_3032)

lemma oc_nc_3033: "oc_sub None 3033"
  by (oc_eval oc_nc_3033)

lemma oc_nc_3034: "oc_sub None 3034"
  by (oc_eval oc_nc_3034)

lemma oc_nc_3035: "oc_sub None 3035"
  by (oc_eval oc_nc_3035)

lemma oc_nc_3036: "oc_sub None 3036"
  by (oc_eval oc_nc_3036)

lemma oc_nc_3037: "oc_sub None 3037"
  by (oc_eval oc_nc_3037)

lemma oc_nc_3038: "oc_sub None 3038"
  by (oc_eval oc_nc_3038)

lemma oc_nc_3039: "oc_sub None 3039"
  by (oc_eval oc_nc_3039)

lemma upt_nc_189: "[3024..<3040] = [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]"
  by (simp add: upt_rec)

lemma sec_nc_189: "\<forall>j\<in>{16 * 189..<16 * 189 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 189..<16 * 189 + 16}"
  then have "j \<in> set [3024..<3040]" unfolding set_upt by simp
  then have "j \<in> set [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]" unfolding upt_nc_189 .
  then show "oc_sub None j" using oc_nc_3024 oc_nc_3025 oc_nc_3026 oc_nc_3027 oc_nc_3028 oc_nc_3029 oc_nc_3030 oc_nc_3031 oc_nc_3032 oc_nc_3033 oc_nc_3034 oc_nc_3035 oc_nc_3036 oc_nc_3037 oc_nc_3038 oc_nc_3039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
