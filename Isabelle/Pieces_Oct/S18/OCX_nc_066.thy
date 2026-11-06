theory OCX_nc_066
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1056: "oc_sub None 1056"
  by (oc_eval oc_nc_1056)

lemma oc_nc_1057: "oc_sub None 1057"
  by (oc_eval oc_nc_1057)

lemma oc_nc_1058: "oc_sub None 1058"
  by (oc_eval oc_nc_1058)

lemma oc_nc_1059: "oc_sub None 1059"
  by (oc_eval oc_nc_1059)

lemma oc_nc_1060: "oc_sub None 1060"
  by (oc_eval oc_nc_1060)

lemma oc_nc_1061: "oc_sub None 1061"
  by (oc_eval oc_nc_1061)

lemma oc_nc_1062: "oc_sub None 1062"
  by (oc_eval oc_nc_1062)

lemma oc_nc_1063: "oc_sub None 1063"
  by (oc_eval oc_nc_1063)

lemma oc_nc_1064: "oc_sub None 1064"
  by (oc_eval oc_nc_1064)

lemma oc_nc_1065: "oc_sub None 1065"
  by (oc_eval oc_nc_1065)

lemma oc_nc_1066: "oc_sub None 1066"
  by (oc_eval oc_nc_1066)

lemma oc_nc_1067: "oc_sub None 1067"
  by (oc_eval oc_nc_1067)

lemma oc_nc_1068: "oc_sub None 1068"
  by (oc_eval oc_nc_1068)

lemma oc_nc_1069: "oc_sub None 1069"
  by (oc_eval oc_nc_1069)

lemma oc_nc_1070: "oc_sub None 1070"
  by (oc_eval oc_nc_1070)

lemma oc_nc_1071: "oc_sub None 1071"
  by (oc_eval oc_nc_1071)

lemma upt_nc_066: "[1056..<1072] = [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]"
  by (simp add: upt_rec)

lemma sec_nc_066: "\<forall>j\<in>{16 * 66..<16 * 66 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 66..<16 * 66 + 16}"
  then have "j \<in> set [1056..<1072]" unfolding set_upt by simp
  then have "j \<in> set [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]" unfolding upt_nc_066 .
  then show "oc_sub None j" using oc_nc_1056 oc_nc_1057 oc_nc_1058 oc_nc_1059 oc_nc_1060 oc_nc_1061 oc_nc_1062 oc_nc_1063 oc_nc_1064 oc_nc_1065 oc_nc_1066 oc_nc_1067 oc_nc_1068 oc_nc_1069 oc_nc_1070 oc_nc_1071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
