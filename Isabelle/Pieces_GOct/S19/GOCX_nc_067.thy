theory GOCX_nc_067
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1072: "goc_sub None 1072"
  by (goc_eval goc_nc_1072)

lemma goc_nc_1073: "goc_sub None 1073"
  by (goc_eval goc_nc_1073)

lemma goc_nc_1074: "goc_sub None 1074"
  by (goc_eval goc_nc_1074)

lemma goc_nc_1075: "goc_sub None 1075"
  by (goc_eval goc_nc_1075)

lemma goc_nc_1076: "goc_sub None 1076"
  by (goc_eval goc_nc_1076)

lemma goc_nc_1077: "goc_sub None 1077"
  by (goc_eval goc_nc_1077)

lemma goc_nc_1078: "goc_sub None 1078"
  by (goc_eval goc_nc_1078)

lemma goc_nc_1079: "goc_sub None 1079"
  by (goc_eval goc_nc_1079)

lemma goc_nc_1080: "goc_sub None 1080"
  by (goc_eval goc_nc_1080)

lemma goc_nc_1081: "goc_sub None 1081"
  by (goc_eval goc_nc_1081)

lemma goc_nc_1082: "goc_sub None 1082"
  by (goc_eval goc_nc_1082)

lemma goc_nc_1083: "goc_sub None 1083"
  by (goc_eval goc_nc_1083)

lemma goc_nc_1084: "goc_sub None 1084"
  by (goc_eval goc_nc_1084)

lemma goc_nc_1085: "goc_sub None 1085"
  by (goc_eval goc_nc_1085)

lemma goc_nc_1086: "goc_sub None 1086"
  by (goc_eval goc_nc_1086)

lemma goc_nc_1087: "goc_sub None 1087"
  by (goc_eval goc_nc_1087)

lemma gupt_nc_067: "[1072..<1088] = [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]"
  by (simp add: upt_rec)

lemma gsec_nc_067: "\<forall>j\<in>{16 * 67..<16 * 67 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 67..<16 * 67 + 16}"
  then have "j \<in> set [1072..<1088]" unfolding set_upt by simp
  then have "j \<in> set [1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087]" unfolding gupt_nc_067 .
  then show "goc_sub None j" using goc_nc_1072 goc_nc_1073 goc_nc_1074 goc_nc_1075 goc_nc_1076 goc_nc_1077 goc_nc_1078 goc_nc_1079 goc_nc_1080 goc_nc_1081 goc_nc_1082 goc_nc_1083 goc_nc_1084 goc_nc_1085 goc_nc_1086 goc_nc_1087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
