theory OCX_nc_070
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1120: "oc_sub None 1120"
  by (oc_eval oc_nc_1120)

lemma oc_nc_1121: "oc_sub None 1121"
  by (oc_eval oc_nc_1121)

lemma oc_nc_1122: "oc_sub None 1122"
  by (oc_eval oc_nc_1122)

lemma oc_nc_1123: "oc_sub None 1123"
  by (oc_eval oc_nc_1123)

lemma oc_nc_1124: "oc_sub None 1124"
  by (oc_eval oc_nc_1124)

lemma oc_nc_1125: "oc_sub None 1125"
  by (oc_eval oc_nc_1125)

lemma oc_nc_1126: "oc_sub None 1126"
  by (oc_eval oc_nc_1126)

lemma oc_nc_1127: "oc_sub None 1127"
  by (oc_eval oc_nc_1127)

lemma oc_nc_1128: "oc_sub None 1128"
  by (oc_eval oc_nc_1128)

lemma oc_nc_1129: "oc_sub None 1129"
  by (oc_eval oc_nc_1129)

lemma oc_nc_1130: "oc_sub None 1130"
  by (oc_eval oc_nc_1130)

lemma oc_nc_1131: "oc_sub None 1131"
  by (oc_eval oc_nc_1131)

lemma oc_nc_1132: "oc_sub None 1132"
  by (oc_eval oc_nc_1132)

lemma oc_nc_1133: "oc_sub None 1133"
  by (oc_eval oc_nc_1133)

lemma oc_nc_1134: "oc_sub None 1134"
  by (oc_eval oc_nc_1134)

lemma oc_nc_1135: "oc_sub None 1135"
  by (oc_eval oc_nc_1135)

lemma upt_nc_070: "[1120..<1136] = [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]"
  by (simp add: upt_rec)

lemma sec_nc_070: "\<forall>j\<in>{16 * 70..<16 * 70 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 70..<16 * 70 + 16}"
  then have "j \<in> set [1120..<1136]" unfolding set_upt by simp
  then have "j \<in> set [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]" unfolding upt_nc_070 .
  then show "oc_sub None j" using oc_nc_1120 oc_nc_1121 oc_nc_1122 oc_nc_1123 oc_nc_1124 oc_nc_1125 oc_nc_1126 oc_nc_1127 oc_nc_1128 oc_nc_1129 oc_nc_1130 oc_nc_1131 oc_nc_1132 oc_nc_1133 oc_nc_1134 oc_nc_1135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
