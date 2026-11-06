theory OCX_c30_071
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1136: "oc_sub oc_b30 1136"
  by (oc_eval oc_c30_1136)

lemma oc_c30_1137: "oc_sub oc_b30 1137"
  by (oc_eval oc_c30_1137)

lemma oc_c30_1138: "oc_sub oc_b30 1138"
  by (oc_eval oc_c30_1138)

lemma oc_c30_1139: "oc_sub oc_b30 1139"
  by (oc_eval oc_c30_1139)

lemma oc_c30_1140: "oc_sub oc_b30 1140"
  by (oc_eval oc_c30_1140)

lemma oc_c30_1141: "oc_sub oc_b30 1141"
  by (oc_eval oc_c30_1141)

lemma oc_c30_1142: "oc_sub oc_b30 1142"
  by (oc_eval oc_c30_1142)

lemma oc_c30_1143: "oc_sub oc_b30 1143"
  by (oc_eval oc_c30_1143)

lemma oc_c30_1144: "oc_sub oc_b30 1144"
  by (oc_eval oc_c30_1144)

lemma oc_c30_1145: "oc_sub oc_b30 1145"
  by (oc_eval oc_c30_1145)

lemma oc_c30_1146: "oc_sub oc_b30 1146"
  by (oc_eval oc_c30_1146)

lemma oc_c30_1147: "oc_sub oc_b30 1147"
  by (oc_eval oc_c30_1147)

lemma oc_c30_1148: "oc_sub oc_b30 1148"
  by (oc_eval oc_c30_1148)

lemma oc_c30_1149: "oc_sub oc_b30 1149"
  by (oc_eval oc_c30_1149)

lemma oc_c30_1150: "oc_sub oc_b30 1150"
  by (oc_eval oc_c30_1150)

lemma oc_c30_1151: "oc_sub oc_b30 1151"
  by (oc_eval oc_c30_1151)

lemma upt_c30_071: "[1136..<1152] = [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]"
  by (simp add: upt_rec)

lemma sec_c30_071: "\<forall>j\<in>{16 * 71..<16 * 71 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 71..<16 * 71 + 16}"
  then have "j \<in> set [1136..<1152]" unfolding set_upt by simp
  then have "j \<in> set [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151]" unfolding upt_c30_071 .
  then show "oc_sub oc_b30 j" using oc_c30_1136 oc_c30_1137 oc_c30_1138 oc_c30_1139 oc_c30_1140 oc_c30_1141 oc_c30_1142 oc_c30_1143 oc_c30_1144 oc_c30_1145 oc_c30_1146 oc_c30_1147 oc_c30_1148 oc_c30_1149 oc_c30_1150 oc_c30_1151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
