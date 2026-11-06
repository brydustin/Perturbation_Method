theory GDCX_nc_066
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1056: "gdc_sub None 1056"
  by (gdc_eval gdc_nc_1056)

lemma gdc_nc_1057: "gdc_sub None 1057"
  by (gdc_eval gdc_nc_1057)

lemma gdc_nc_1058: "gdc_sub None 1058"
  by (gdc_eval gdc_nc_1058)

lemma gdc_nc_1059: "gdc_sub None 1059"
  by (gdc_eval gdc_nc_1059)

lemma gdc_nc_1060: "gdc_sub None 1060"
  by (gdc_eval gdc_nc_1060)

lemma gdc_nc_1061: "gdc_sub None 1061"
  by (gdc_eval gdc_nc_1061)

lemma gdc_nc_1062: "gdc_sub None 1062"
  by (gdc_eval gdc_nc_1062)

lemma gdc_nc_1063: "gdc_sub None 1063"
  by (gdc_eval gdc_nc_1063)

lemma gdc_nc_1064: "gdc_sub None 1064"
  by (gdc_eval gdc_nc_1064)

lemma gdc_nc_1065: "gdc_sub None 1065"
  by (gdc_eval gdc_nc_1065)

lemma gdc_nc_1066: "gdc_sub None 1066"
  by (gdc_eval gdc_nc_1066)

lemma gdc_nc_1067: "gdc_sub None 1067"
  by (gdc_eval gdc_nc_1067)

lemma gdc_nc_1068: "gdc_sub None 1068"
  by (gdc_eval gdc_nc_1068)

lemma gdc_nc_1069: "gdc_sub None 1069"
  by (gdc_eval gdc_nc_1069)

lemma gdc_nc_1070: "gdc_sub None 1070"
  by (gdc_eval gdc_nc_1070)

lemma gdc_nc_1071: "gdc_sub None 1071"
  by (gdc_eval gdc_nc_1071)

lemma gupt_nc_066: "[1056..<1072] = [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]"
  by (simp add: upt_rec)

lemma gsec_nc_066: "\<forall>j\<in>{16 * 66..<16 * 66 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 66..<16 * 66 + 16}"
  then have "j \<in> set [1056..<1072]" unfolding set_upt by simp
  then have "j \<in> set [1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071]" unfolding gupt_nc_066 .
  then show "gdc_sub None j" using gdc_nc_1056 gdc_nc_1057 gdc_nc_1058 gdc_nc_1059 gdc_nc_1060 gdc_nc_1061 gdc_nc_1062 gdc_nc_1063 gdc_nc_1064 gdc_nc_1065 gdc_nc_1066 gdc_nc_1067 gdc_nc_1068 gdc_nc_1069 gdc_nc_1070 gdc_nc_1071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
