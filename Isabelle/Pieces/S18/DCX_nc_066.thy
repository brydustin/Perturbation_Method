theory DCX_nc_066
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1056: "dc_sub None 1056"
  by (dc_eval dc_nc_1056)

lemma dc_nc_1057: "dc_sub None 1057"
  by (dc_eval dc_nc_1057)

lemma dc_nc_1058: "dc_sub None 1058"
  by (dc_eval dc_nc_1058)

lemma dc_nc_1059: "dc_sub None 1059"
  by (dc_eval dc_nc_1059)

lemma dc_nc_1060: "dc_sub None 1060"
  by (dc_eval dc_nc_1060)

lemma dc_nc_1061: "dc_sub None 1061"
  by (dc_eval dc_nc_1061)

lemma dc_nc_1062: "dc_sub None 1062"
  by (dc_eval dc_nc_1062)

lemma dc_nc_1063: "dc_sub None 1063"
  by (dc_eval dc_nc_1063)

lemma dc_nc_1064: "dc_sub None 1064"
  by (dc_eval dc_nc_1064)

lemma dc_nc_1065: "dc_sub None 1065"
  by (dc_eval dc_nc_1065)

lemma dc_nc_1066: "dc_sub None 1066"
  by (dc_eval dc_nc_1066)

lemma dc_nc_1067: "dc_sub None 1067"
  by (dc_eval dc_nc_1067)

lemma dc_nc_1068: "dc_sub None 1068"
  by (dc_eval dc_nc_1068)

lemma dc_nc_1069: "dc_sub None 1069"
  by (dc_eval dc_nc_1069)

lemma dc_nc_1070: "dc_sub None 1070"
  by (dc_eval dc_nc_1070)

lemma dc_nc_1071: "dc_sub None 1071"
  by (dc_eval dc_nc_1071)

lemma upt_nc_066: "[1056..<1072] = [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]"
  by (simp add: upt_rec)

lemma sec_nc_066: "\<forall>j\<in>{16 * 66..<16 * 66 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 66..<16 * 66 + 16}"
  then have "j \<in> set [1056..<1072]" unfolding set_upt by simp
  then have "j \<in> set [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]" unfolding upt_nc_066 .
  then show "dc_sub None j" using dc_nc_1056 dc_nc_1057 dc_nc_1058 dc_nc_1059 dc_nc_1060 dc_nc_1061 dc_nc_1062 dc_nc_1063 dc_nc_1064 dc_nc_1065 dc_nc_1066 dc_nc_1067 dc_nc_1068 dc_nc_1069 dc_nc_1070 dc_nc_1071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
