theory OCX_c30_067
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1072: "oc_sub oc_b30 1072"
  by (oc_eval oc_c30_1072)

lemma oc_c30_1073: "oc_sub oc_b30 1073"
  by (oc_eval oc_c30_1073)

lemma oc_c30_1074: "oc_sub oc_b30 1074"
  by (oc_eval oc_c30_1074)

lemma oc_c30_1075: "oc_sub oc_b30 1075"
  by (oc_eval oc_c30_1075)

lemma oc_c30_1076: "oc_sub oc_b30 1076"
  by (oc_eval oc_c30_1076)

lemma oc_c30_1077: "oc_sub oc_b30 1077"
  by (oc_eval oc_c30_1077)

lemma oc_c30_1078: "oc_sub oc_b30 1078"
  by (oc_eval oc_c30_1078)

lemma oc_c30_1079: "oc_sub oc_b30 1079"
  by (oc_eval oc_c30_1079)

lemma oc_c30_1080: "oc_sub oc_b30 1080"
  by (oc_eval oc_c30_1080)

lemma oc_c30_1081: "oc_sub oc_b30 1081"
  by (oc_eval oc_c30_1081)

lemma oc_c30_1082: "oc_sub oc_b30 1082"
  by (oc_eval oc_c30_1082)

lemma oc_c30_1083: "oc_sub oc_b30 1083"
  by (oc_eval oc_c30_1083)

lemma oc_c30_1084: "oc_sub oc_b30 1084"
  by (oc_eval oc_c30_1084)

lemma oc_c30_1085: "oc_sub oc_b30 1085"
  by (oc_eval oc_c30_1085)

lemma oc_c30_1086: "oc_sub oc_b30 1086"
  by (oc_eval oc_c30_1086)

lemma oc_c30_1087: "oc_sub oc_b30 1087"
  by (oc_eval oc_c30_1087)

lemma upt_c30_067: "[1072..<1088] = [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]"
  by (simp add: upt_rec)

lemma sec_c30_067: "\<forall>j\<in>{16 * 67..<16 * 67 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 67..<16 * 67 + 16}"
  then have "j \<in> set [1072..<1088]" unfolding set_upt by simp
  then have "j \<in> set [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]" unfolding upt_c30_067 .
  then show "oc_sub oc_b30 j" using oc_c30_1072 oc_c30_1073 oc_c30_1074 oc_c30_1075 oc_c30_1076 oc_c30_1077 oc_c30_1078 oc_c30_1079 oc_c30_1080 oc_c30_1081 oc_c30_1082 oc_c30_1083 oc_c30_1084 oc_c30_1085 oc_c30_1086 oc_c30_1087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
