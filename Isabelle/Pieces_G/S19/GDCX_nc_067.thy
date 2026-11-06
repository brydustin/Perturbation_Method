theory GDCX_nc_067
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1072: "gdc_sub None 1072"
  by (gdc_eval gdc_nc_1072)

lemma gdc_nc_1073: "gdc_sub None 1073"
  by (gdc_eval gdc_nc_1073)

lemma gdc_nc_1074: "gdc_sub None 1074"
  by (gdc_eval gdc_nc_1074)

lemma gdc_nc_1075: "gdc_sub None 1075"
  by (gdc_eval gdc_nc_1075)

lemma gdc_nc_1076: "gdc_sub None 1076"
  by (gdc_eval gdc_nc_1076)

lemma gdc_nc_1077: "gdc_sub None 1077"
  by (gdc_eval gdc_nc_1077)

lemma gdc_nc_1078: "gdc_sub None 1078"
  by (gdc_eval gdc_nc_1078)

lemma gdc_nc_1079: "gdc_sub None 1079"
  by (gdc_eval gdc_nc_1079)

lemma gdc_nc_1080: "gdc_sub None 1080"
  by (gdc_eval gdc_nc_1080)

lemma gdc_nc_1081: "gdc_sub None 1081"
  by (gdc_eval gdc_nc_1081)

lemma gdc_nc_1082: "gdc_sub None 1082"
  by (gdc_eval gdc_nc_1082)

lemma gdc_nc_1083: "gdc_sub None 1083"
  by (gdc_eval gdc_nc_1083)

lemma gdc_nc_1084: "gdc_sub None 1084"
  by (gdc_eval gdc_nc_1084)

lemma gdc_nc_1085: "gdc_sub None 1085"
  by (gdc_eval gdc_nc_1085)

lemma gdc_nc_1086: "gdc_sub None 1086"
  by (gdc_eval gdc_nc_1086)

lemma gdc_nc_1087: "gdc_sub None 1087"
  by (gdc_eval gdc_nc_1087)

lemma gupt_nc_067: "[1072..<1088] = [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]"
  by (simp add: upt_rec)

lemma gsec_nc_067: "\<forall>j\<in>{16 * 67..<16 * 67 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 67..<16 * 67 + 16}"
  then have "j \<in> set [1072..<1088]" unfolding set_upt by simp
  then have "j \<in> set [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]" unfolding gupt_nc_067 .
  then show "gdc_sub None j" using gdc_nc_1072 gdc_nc_1073 gdc_nc_1074 gdc_nc_1075 gdc_nc_1076 gdc_nc_1077 gdc_nc_1078 gdc_nc_1079 gdc_nc_1080 gdc_nc_1081 gdc_nc_1082 gdc_nc_1083 gdc_nc_1084 gdc_nc_1085 gdc_nc_1086 gdc_nc_1087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
