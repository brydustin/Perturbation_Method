theory DCX_nc_071
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1136: "dc_sub None 1136"
  by (dc_eval dc_nc_1136)

lemma dc_nc_1137: "dc_sub None 1137"
  by (dc_eval dc_nc_1137)

lemma dc_nc_1138: "dc_sub None 1138"
  by (dc_eval dc_nc_1138)

lemma dc_nc_1139: "dc_sub None 1139"
  by (dc_eval dc_nc_1139)

lemma dc_nc_1140: "dc_sub None 1140"
  by (dc_eval dc_nc_1140)

lemma dc_nc_1141: "dc_sub None 1141"
  by (dc_eval dc_nc_1141)

lemma dc_nc_1142: "dc_sub None 1142"
  by (dc_eval dc_nc_1142)

lemma dc_nc_1143: "dc_sub None 1143"
  by (dc_eval dc_nc_1143)

lemma dc_nc_1144: "dc_sub None 1144"
  by (dc_eval dc_nc_1144)

lemma dc_nc_1145: "dc_sub None 1145"
  by (dc_eval dc_nc_1145)

lemma dc_nc_1146: "dc_sub None 1146"
  by (dc_eval dc_nc_1146)

lemma dc_nc_1147: "dc_sub None 1147"
  by (dc_eval dc_nc_1147)

lemma dc_nc_1148: "dc_sub None 1148"
  by (dc_eval dc_nc_1148)

lemma dc_nc_1149: "dc_sub None 1149"
  by (dc_eval dc_nc_1149)

lemma dc_nc_1150: "dc_sub None 1150"
  by (dc_eval dc_nc_1150)

lemma dc_nc_1151: "dc_sub None 1151"
  by (dc_eval dc_nc_1151)

lemma upt_nc_071: "[1136..<1152] = [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]"
  by (simp add: upt_rec)

lemma sec_nc_071: "\<forall>j\<in>{16 * 71..<16 * 71 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 71..<16 * 71 + 16}"
  then have "j \<in> set [1136..<1152]" unfolding set_upt by simp
  then have "j \<in> set [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]" unfolding upt_nc_071 .
  then show "dc_sub None j" using dc_nc_1136 dc_nc_1137 dc_nc_1138 dc_nc_1139 dc_nc_1140 dc_nc_1141 dc_nc_1142 dc_nc_1143 dc_nc_1144 dc_nc_1145 dc_nc_1146 dc_nc_1147 dc_nc_1148 dc_nc_1149 dc_nc_1150 dc_nc_1151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
