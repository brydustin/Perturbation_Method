theory DCX_c30_067
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1072: "dc_sub dc_b30 1072"
  by (dc_eval dc_c30_1072)

lemma dc_c30_1073: "dc_sub dc_b30 1073"
  by (dc_eval dc_c30_1073)

lemma dc_c30_1074: "dc_sub dc_b30 1074"
  by (dc_eval dc_c30_1074)

lemma dc_c30_1075: "dc_sub dc_b30 1075"
  by (dc_eval dc_c30_1075)

lemma dc_c30_1076: "dc_sub dc_b30 1076"
  by (dc_eval dc_c30_1076)

lemma dc_c30_1077: "dc_sub dc_b30 1077"
  by (dc_eval dc_c30_1077)

lemma dc_c30_1078: "dc_sub dc_b30 1078"
  by (dc_eval dc_c30_1078)

lemma dc_c30_1079: "dc_sub dc_b30 1079"
  by (dc_eval dc_c30_1079)

lemma dc_c30_1080: "dc_sub dc_b30 1080"
  by (dc_eval dc_c30_1080)

lemma dc_c30_1081: "dc_sub dc_b30 1081"
  by (dc_eval dc_c30_1081)

lemma dc_c30_1082: "dc_sub dc_b30 1082"
  by (dc_eval dc_c30_1082)

lemma dc_c30_1083: "dc_sub dc_b30 1083"
  by (dc_eval dc_c30_1083)

lemma dc_c30_1084: "dc_sub dc_b30 1084"
  by (dc_eval dc_c30_1084)

lemma dc_c30_1085: "dc_sub dc_b30 1085"
  by (dc_eval dc_c30_1085)

lemma dc_c30_1086: "dc_sub dc_b30 1086"
  by (dc_eval dc_c30_1086)

lemma dc_c30_1087: "dc_sub dc_b30 1087"
  by (dc_eval dc_c30_1087)

lemma upt_c30_067: "[1072..<1088] = [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]"
  by (simp add: upt_rec)

lemma sec_c30_067: "\<forall>j\<in>{16 * 67..<16 * 67 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 67..<16 * 67 + 16}"
  then have "j \<in> set [1072..<1088]" unfolding set_upt by simp
  then have "j \<in> set [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]" unfolding upt_c30_067 .
  then show "dc_sub dc_b30 j" using dc_c30_1072 dc_c30_1073 dc_c30_1074 dc_c30_1075 dc_c30_1076 dc_c30_1077 dc_c30_1078 dc_c30_1079 dc_c30_1080 dc_c30_1081 dc_c30_1082 dc_c30_1083 dc_c30_1084 dc_c30_1085 dc_c30_1086 dc_c30_1087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
