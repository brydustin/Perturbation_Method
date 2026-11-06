theory OCX_c30_189
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3024: "oc_sub oc_b30 3024"
  by (oc_eval oc_c30_3024)

lemma oc_c30_3025: "oc_sub oc_b30 3025"
  by (oc_eval oc_c30_3025)

lemma oc_c30_3026: "oc_sub oc_b30 3026"
  by (oc_eval oc_c30_3026)

lemma oc_c30_3027: "oc_sub oc_b30 3027"
  by (oc_eval oc_c30_3027)

lemma oc_c30_3028: "oc_sub oc_b30 3028"
  by (oc_eval oc_c30_3028)

lemma oc_c30_3029: "oc_sub oc_b30 3029"
  by (oc_eval oc_c30_3029)

lemma oc_c30_3030: "oc_sub oc_b30 3030"
  by (oc_eval oc_c30_3030)

lemma oc_c30_3031: "oc_sub oc_b30 3031"
  by (oc_eval oc_c30_3031)

lemma oc_c30_3032: "oc_sub oc_b30 3032"
  by (oc_eval oc_c30_3032)

lemma oc_c30_3033: "oc_sub oc_b30 3033"
  by (oc_eval oc_c30_3033)

lemma oc_c30_3034: "oc_sub oc_b30 3034"
  by (oc_eval oc_c30_3034)

lemma oc_c30_3035: "oc_sub oc_b30 3035"
  by (oc_eval oc_c30_3035)

lemma oc_c30_3036: "oc_sub oc_b30 3036"
  by (oc_eval oc_c30_3036)

lemma oc_c30_3037: "oc_sub oc_b30 3037"
  by (oc_eval oc_c30_3037)

lemma oc_c30_3038: "oc_sub oc_b30 3038"
  by (oc_eval oc_c30_3038)

lemma oc_c30_3039: "oc_sub oc_b30 3039"
  by (oc_eval oc_c30_3039)

lemma upt_c30_189: "[3024..<3040] = [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]"
  by (simp add: upt_rec)

lemma sec_c30_189: "\<forall>j\<in>{16 * 189..<16 * 189 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 189..<16 * 189 + 16}"
  then have "j \<in> set [3024..<3040]" unfolding set_upt by simp
  then have "j \<in> set [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]" unfolding upt_c30_189 .
  then show "oc_sub oc_b30 j" using oc_c30_3024 oc_c30_3025 oc_c30_3026 oc_c30_3027 oc_c30_3028 oc_c30_3029 oc_c30_3030 oc_c30_3031 oc_c30_3032 oc_c30_3033 oc_c30_3034 oc_c30_3035 oc_c30_3036 oc_c30_3037 oc_c30_3038 oc_c30_3039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
