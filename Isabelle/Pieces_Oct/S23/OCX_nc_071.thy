theory OCX_nc_071
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1136: "oc_sub None 1136"
  by (oc_eval oc_nc_1136)

lemma oc_nc_1137: "oc_sub None 1137"
  by (oc_eval oc_nc_1137)

lemma oc_nc_1138: "oc_sub None 1138"
  by (oc_eval oc_nc_1138)

lemma oc_nc_1139: "oc_sub None 1139"
  by (oc_eval oc_nc_1139)

lemma oc_nc_1140: "oc_sub None 1140"
  by (oc_eval oc_nc_1140)

lemma oc_nc_1141: "oc_sub None 1141"
  by (oc_eval oc_nc_1141)

lemma oc_nc_1142: "oc_sub None 1142"
  by (oc_eval oc_nc_1142)

lemma oc_nc_1143: "oc_sub None 1143"
  by (oc_eval oc_nc_1143)

lemma oc_nc_1144: "oc_sub None 1144"
  by (oc_eval oc_nc_1144)

lemma oc_nc_1145: "oc_sub None 1145"
  by (oc_eval oc_nc_1145)

lemma oc_nc_1146: "oc_sub None 1146"
  by (oc_eval oc_nc_1146)

lemma oc_nc_1147: "oc_sub None 1147"
  by (oc_eval oc_nc_1147)

lemma oc_nc_1148: "oc_sub None 1148"
  by (oc_eval oc_nc_1148)

lemma oc_nc_1149: "oc_sub None 1149"
  by (oc_eval oc_nc_1149)

lemma oc_nc_1150: "oc_sub None 1150"
  by (oc_eval oc_nc_1150)

lemma oc_nc_1151: "oc_sub None 1151"
  by (oc_eval oc_nc_1151)

lemma upt_nc_071: "[1136..<1152] = [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]"
  by (simp add: upt_rec)

lemma sec_nc_071: "\<forall>j\<in>{16 * 71..<16 * 71 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 71..<16 * 71 + 16}"
  then have "j \<in> set [1136..<1152]" unfolding set_upt by simp
  then have "j \<in> set [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]" unfolding upt_nc_071 .
  then show "oc_sub None j" using oc_nc_1136 oc_nc_1137 oc_nc_1138 oc_nc_1139 oc_nc_1140 oc_nc_1141 oc_nc_1142 oc_nc_1143 oc_nc_1144 oc_nc_1145 oc_nc_1146 oc_nc_1147 oc_nc_1148 oc_nc_1149 oc_nc_1150 oc_nc_1151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
