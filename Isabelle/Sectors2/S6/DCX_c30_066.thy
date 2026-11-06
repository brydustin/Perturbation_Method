theory DCX_c30_066
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1056: "dc_sub dc_b30 1056"
  by (dc_eval dc_c30_1056)

lemma dc_c30_1057: "dc_sub dc_b30 1057"
  by (dc_eval dc_c30_1057)

lemma dc_c30_1058: "dc_sub dc_b30 1058"
  by (dc_eval dc_c30_1058)

lemma dc_c30_1059: "dc_sub dc_b30 1059"
  by (dc_eval dc_c30_1059)

lemma dc_c30_1060: "dc_sub dc_b30 1060"
  by (dc_eval dc_c30_1060)

lemma dc_c30_1061: "dc_sub dc_b30 1061"
  by (dc_eval dc_c30_1061)

lemma dc_c30_1062: "dc_sub dc_b30 1062"
  by (dc_eval dc_c30_1062)

lemma dc_c30_1063: "dc_sub dc_b30 1063"
  by (dc_eval dc_c30_1063)

lemma dc_c30_1064: "dc_sub dc_b30 1064"
  by (dc_eval dc_c30_1064)

lemma dc_c30_1065: "dc_sub dc_b30 1065"
  by (dc_eval dc_c30_1065)

lemma dc_c30_1066: "dc_sub dc_b30 1066"
  by (dc_eval dc_c30_1066)

lemma dc_c30_1067: "dc_sub dc_b30 1067"
  by (dc_eval dc_c30_1067)

lemma dc_c30_1068: "dc_sub dc_b30 1068"
  by (dc_eval dc_c30_1068)

lemma dc_c30_1069: "dc_sub dc_b30 1069"
  by (dc_eval dc_c30_1069)

lemma dc_c30_1070: "dc_sub dc_b30 1070"
  by (dc_eval dc_c30_1070)

lemma dc_c30_1071: "dc_sub dc_b30 1071"
  by (dc_eval dc_c30_1071)

lemma upt_c30_066: "[1056..<1072] = [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]"
  by (simp add: upt_rec)

lemma sec_c30_066: "\<forall>j\<in>{16 * 66..<16 * 66 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 66..<16 * 66 + 16}"
  then have "j \<in> set [1056..<1072]" unfolding set_upt by simp
  then have "j \<in> set [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]" unfolding upt_c30_066 .
  then show "dc_sub dc_b30 j" using dc_c30_1056 dc_c30_1057 dc_c30_1058 dc_c30_1059 dc_c30_1060 dc_c30_1061 dc_c30_1062 dc_c30_1063 dc_c30_1064 dc_c30_1065 dc_c30_1066 dc_c30_1067 dc_c30_1068 dc_c30_1069 dc_c30_1070 dc_c30_1071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
