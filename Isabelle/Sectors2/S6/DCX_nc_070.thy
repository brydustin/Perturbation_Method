theory DCX_nc_070
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1120: "dc_sub None 1120"
  by (dc_eval dc_nc_1120)

lemma dc_nc_1121: "dc_sub None 1121"
  by (dc_eval dc_nc_1121)

lemma dc_nc_1122: "dc_sub None 1122"
  by (dc_eval dc_nc_1122)

lemma dc_nc_1123: "dc_sub None 1123"
  by (dc_eval dc_nc_1123)

lemma dc_nc_1124: "dc_sub None 1124"
  by (dc_eval dc_nc_1124)

lemma dc_nc_1125: "dc_sub None 1125"
  by (dc_eval dc_nc_1125)

lemma dc_nc_1126: "dc_sub None 1126"
  by (dc_eval dc_nc_1126)

lemma dc_nc_1127: "dc_sub None 1127"
  by (dc_eval dc_nc_1127)

lemma dc_nc_1128: "dc_sub None 1128"
  by (dc_eval dc_nc_1128)

lemma dc_nc_1129: "dc_sub None 1129"
  by (dc_eval dc_nc_1129)

lemma dc_nc_1130: "dc_sub None 1130"
  by (dc_eval dc_nc_1130)

lemma dc_nc_1131: "dc_sub None 1131"
  by (dc_eval dc_nc_1131)

lemma dc_nc_1132: "dc_sub None 1132"
  by (dc_eval dc_nc_1132)

lemma dc_nc_1133: "dc_sub None 1133"
  by (dc_eval dc_nc_1133)

lemma dc_nc_1134: "dc_sub None 1134"
  by (dc_eval dc_nc_1134)

lemma dc_nc_1135: "dc_sub None 1135"
  by (dc_eval dc_nc_1135)

lemma upt_nc_070: "[1120..<1136] = [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]"
  by (simp add: upt_rec)

lemma sec_nc_070: "\<forall>j\<in>{16 * 70..<16 * 70 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 70..<16 * 70 + 16}"
  then have "j \<in> set [1120..<1136]" unfolding set_upt by simp
  then have "j \<in> set [1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135]" unfolding upt_nc_070 .
  then show "dc_sub None j" using dc_nc_1120 dc_nc_1121 dc_nc_1122 dc_nc_1123 dc_nc_1124 dc_nc_1125 dc_nc_1126 dc_nc_1127 dc_nc_1128 dc_nc_1129 dc_nc_1130 dc_nc_1131 dc_nc_1132 dc_nc_1133 dc_nc_1134 dc_nc_1135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
