theory GOCX_nc_066
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1056: "goc_sub None 1056"
  by (goc_eval goc_nc_1056)

lemma goc_nc_1057: "goc_sub None 1057"
  by (goc_eval goc_nc_1057)

lemma goc_nc_1058: "goc_sub None 1058"
  by (goc_eval goc_nc_1058)

lemma goc_nc_1059: "goc_sub None 1059"
  by (goc_eval goc_nc_1059)

lemma goc_nc_1060: "goc_sub None 1060"
  by (goc_eval goc_nc_1060)

lemma goc_nc_1061: "goc_sub None 1061"
  by (goc_eval goc_nc_1061)

lemma goc_nc_1062: "goc_sub None 1062"
  by (goc_eval goc_nc_1062)

lemma goc_nc_1063: "goc_sub None 1063"
  by (goc_eval goc_nc_1063)

lemma goc_nc_1064: "goc_sub None 1064"
  by (goc_eval goc_nc_1064)

lemma goc_nc_1065: "goc_sub None 1065"
  by (goc_eval goc_nc_1065)

lemma goc_nc_1066: "goc_sub None 1066"
  by (goc_eval goc_nc_1066)

lemma goc_nc_1067: "goc_sub None 1067"
  by (goc_eval goc_nc_1067)

lemma goc_nc_1068: "goc_sub None 1068"
  by (goc_eval goc_nc_1068)

lemma goc_nc_1069: "goc_sub None 1069"
  by (goc_eval goc_nc_1069)

lemma goc_nc_1070: "goc_sub None 1070"
  by (goc_eval goc_nc_1070)

lemma goc_nc_1071: "goc_sub None 1071"
  by (goc_eval goc_nc_1071)

lemma gupt_nc_066: "[1056..<1072] = [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]"
  by (simp add: upt_rec)

lemma gsec_nc_066: "\<forall>j\<in>{16 * 66..<16 * 66 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 66..<16 * 66 + 16}"
  then have "j \<in> set [1056..<1072]" unfolding set_upt by simp
  then have "j \<in> set [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]" unfolding gupt_nc_066 .
  then show "goc_sub None j" using goc_nc_1056 goc_nc_1057 goc_nc_1058 goc_nc_1059 goc_nc_1060 goc_nc_1061 goc_nc_1062 goc_nc_1063 goc_nc_1064 goc_nc_1065 goc_nc_1066 goc_nc_1067 goc_nc_1068 goc_nc_1069 goc_nc_1070 goc_nc_1071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
