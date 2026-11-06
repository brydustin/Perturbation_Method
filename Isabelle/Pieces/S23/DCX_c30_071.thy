theory DCX_c30_071
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1136: "dc_sub dc_b30 1136"
  by (dc_eval dc_c30_1136)

lemma dc_c30_1137: "dc_sub dc_b30 1137"
  by (dc_eval dc_c30_1137)

lemma dc_c30_1138: "dc_sub dc_b30 1138"
  by (dc_eval dc_c30_1138)

lemma dc_c30_1139: "dc_sub dc_b30 1139"
  by (dc_eval dc_c30_1139)

lemma dc_c30_1140: "dc_sub dc_b30 1140"
  by (dc_eval dc_c30_1140)

lemma dc_c30_1141: "dc_sub dc_b30 1141"
  by (dc_eval dc_c30_1141)

lemma dc_c30_1142: "dc_sub dc_b30 1142"
  by (dc_eval dc_c30_1142)

lemma dc_c30_1143: "dc_sub dc_b30 1143"
  by (dc_eval dc_c30_1143)

lemma dc_c30_1144: "dc_sub dc_b30 1144"
  by (dc_eval dc_c30_1144)

lemma dc_c30_1145: "dc_sub dc_b30 1145"
  by (dc_eval dc_c30_1145)

lemma dc_c30_1146: "dc_sub dc_b30 1146"
  by (dc_eval dc_c30_1146)

lemma dc_c30_1147: "dc_sub dc_b30 1147"
  by (dc_eval dc_c30_1147)

lemma dc_c30_1148: "dc_sub dc_b30 1148"
  by (dc_eval dc_c30_1148)

lemma dc_c30_1149: "dc_sub dc_b30 1149"
  by (dc_eval dc_c30_1149)

lemma dc_c30_1150: "dc_sub dc_b30 1150"
  by (dc_eval dc_c30_1150)

lemma dc_c30_1151: "dc_sub dc_b30 1151"
  by (dc_eval dc_c30_1151)

lemma upt_c30_071: "[1136..<1152] = [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]"
  by (simp add: upt_rec)

lemma sec_c30_071: "\<forall>j\<in>{16 * 71..<16 * 71 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 71..<16 * 71 + 16}"
  then have "j \<in> set [1136..<1152]" unfolding set_upt by simp
  then have "j \<in> set [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]" unfolding upt_c30_071 .
  then show "dc_sub dc_b30 j" using dc_c30_1136 dc_c30_1137 dc_c30_1138 dc_c30_1139 dc_c30_1140 dc_c30_1141 dc_c30_1142 dc_c30_1143 dc_c30_1144 dc_c30_1145 dc_c30_1146 dc_c30_1147 dc_c30_1148 dc_c30_1149 dc_c30_1150 dc_c30_1151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
