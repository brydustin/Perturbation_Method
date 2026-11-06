theory OCX_nc_067
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1072: "oc_sub None 1072"
  by (oc_eval oc_nc_1072)

lemma oc_nc_1073: "oc_sub None 1073"
  by (oc_eval oc_nc_1073)

lemma oc_nc_1074: "oc_sub None 1074"
  by (oc_eval oc_nc_1074)

lemma oc_nc_1075: "oc_sub None 1075"
  by (oc_eval oc_nc_1075)

lemma oc_nc_1076: "oc_sub None 1076"
  by (oc_eval oc_nc_1076)

lemma oc_nc_1077: "oc_sub None 1077"
  by (oc_eval oc_nc_1077)

lemma oc_nc_1078: "oc_sub None 1078"
  by (oc_eval oc_nc_1078)

lemma oc_nc_1079: "oc_sub None 1079"
  by (oc_eval oc_nc_1079)

lemma oc_nc_1080: "oc_sub None 1080"
  by (oc_eval oc_nc_1080)

lemma oc_nc_1081: "oc_sub None 1081"
  by (oc_eval oc_nc_1081)

lemma oc_nc_1082: "oc_sub None 1082"
  by (oc_eval oc_nc_1082)

lemma oc_nc_1083: "oc_sub None 1083"
  by (oc_eval oc_nc_1083)

lemma oc_nc_1084: "oc_sub None 1084"
  by (oc_eval oc_nc_1084)

lemma oc_nc_1085: "oc_sub None 1085"
  by (oc_eval oc_nc_1085)

lemma oc_nc_1086: "oc_sub None 1086"
  by (oc_eval oc_nc_1086)

lemma oc_nc_1087: "oc_sub None 1087"
  by (oc_eval oc_nc_1087)

lemma upt_nc_067: "[1072..<1088] = [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]"
  by (simp add: upt_rec)

lemma sec_nc_067: "\<forall>j\<in>{16 * 67..<16 * 67 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 67..<16 * 67 + 16}"
  then have "j \<in> set [1072..<1088]" unfolding set_upt by simp
  then have "j \<in> set [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]" unfolding upt_nc_067 .
  then show "oc_sub None j" using oc_nc_1072 oc_nc_1073 oc_nc_1074 oc_nc_1075 oc_nc_1076 oc_nc_1077 oc_nc_1078 oc_nc_1079 oc_nc_1080 oc_nc_1081 oc_nc_1082 oc_nc_1083 oc_nc_1084 oc_nc_1085 oc_nc_1086 oc_nc_1087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
