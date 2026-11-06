theory DCX_nc_067
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1072: "dc_sub None 1072"
  by (dc_eval dc_nc_1072)

lemma dc_nc_1073: "dc_sub None 1073"
  by (dc_eval dc_nc_1073)

lemma dc_nc_1074: "dc_sub None 1074"
  by (dc_eval dc_nc_1074)

lemma dc_nc_1075: "dc_sub None 1075"
  by (dc_eval dc_nc_1075)

lemma dc_nc_1076: "dc_sub None 1076"
  by (dc_eval dc_nc_1076)

lemma dc_nc_1077: "dc_sub None 1077"
  by (dc_eval dc_nc_1077)

lemma dc_nc_1078: "dc_sub None 1078"
  by (dc_eval dc_nc_1078)

lemma dc_nc_1079: "dc_sub None 1079"
  by (dc_eval dc_nc_1079)

lemma dc_nc_1080: "dc_sub None 1080"
  by (dc_eval dc_nc_1080)

lemma dc_nc_1081: "dc_sub None 1081"
  by (dc_eval dc_nc_1081)

lemma dc_nc_1082: "dc_sub None 1082"
  by (dc_eval dc_nc_1082)

lemma dc_nc_1083: "dc_sub None 1083"
  by (dc_eval dc_nc_1083)

lemma dc_nc_1084: "dc_sub None 1084"
  by (dc_eval dc_nc_1084)

lemma dc_nc_1085: "dc_sub None 1085"
  by (dc_eval dc_nc_1085)

lemma dc_nc_1086: "dc_sub None 1086"
  by (dc_eval dc_nc_1086)

lemma dc_nc_1087: "dc_sub None 1087"
  by (dc_eval dc_nc_1087)

lemma upt_nc_067: "[1072..<1088] = [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]"
  by (simp add: upt_rec)

lemma sec_nc_067: "\<forall>j\<in>{16 * 67..<16 * 67 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 67..<16 * 67 + 16}"
  then have "j \<in> set [1072..<1088]" unfolding set_upt by simp
  then have "j \<in> set [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]" unfolding upt_nc_067 .
  then show "dc_sub None j" using dc_nc_1072 dc_nc_1073 dc_nc_1074 dc_nc_1075 dc_nc_1076 dc_nc_1077 dc_nc_1078 dc_nc_1079 dc_nc_1080 dc_nc_1081 dc_nc_1082 dc_nc_1083 dc_nc_1084 dc_nc_1085 dc_nc_1086 dc_nc_1087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
