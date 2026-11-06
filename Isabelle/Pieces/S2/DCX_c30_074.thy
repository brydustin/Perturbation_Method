theory DCX_c30_074
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1184: "dc_sub dc_b30 1184"
  by (dc_eval dc_c30_1184)

lemma dc_c30_1185: "dc_sub dc_b30 1185"
  by (dc_eval dc_c30_1185)

lemma dc_c30_1186: "dc_sub dc_b30 1186"
  by (dc_eval dc_c30_1186)

lemma dc_c30_1187: "dc_sub dc_b30 1187"
  by (dc_eval dc_c30_1187)

lemma dc_c30_1188: "dc_sub dc_b30 1188"
  by (dc_eval dc_c30_1188)

lemma dc_c30_1189: "dc_sub dc_b30 1189"
  by (dc_eval dc_c30_1189)

lemma dc_c30_1190: "dc_sub dc_b30 1190"
  by (dc_eval dc_c30_1190)

lemma dc_c30_1191: "dc_sub dc_b30 1191"
  by (dc_eval dc_c30_1191)

lemma dc_c30_1192: "dc_sub dc_b30 1192"
  by (dc_eval dc_c30_1192)

lemma dc_c30_1193: "dc_sub dc_b30 1193"
  by (dc_eval dc_c30_1193)

lemma dc_c30_1194: "dc_sub dc_b30 1194"
  by (dc_eval dc_c30_1194)

lemma dc_c30_1195: "dc_sub dc_b30 1195"
  by (dc_eval dc_c30_1195)

lemma dc_c30_1196: "dc_sub dc_b30 1196"
  by (dc_eval dc_c30_1196)

lemma dc_c30_1197: "dc_sub dc_b30 1197"
  by (dc_eval dc_c30_1197)

lemma dc_c30_1198: "dc_sub dc_b30 1198"
  by (dc_eval dc_c30_1198)

lemma dc_c30_1199: "dc_sub dc_b30 1199"
  by (dc_eval dc_c30_1199)

lemma upt_c30_074: "[1184..<1200] = [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]"
  by (simp add: upt_rec)

lemma sec_c30_074: "\<forall>j\<in>{16 * 74..<16 * 74 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 74..<16 * 74 + 16}"
  then have "j \<in> set [1184..<1200]" unfolding set_upt by simp
  then have "j \<in> set [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]" unfolding upt_c30_074 .
  then show "dc_sub dc_b30 j" using dc_c30_1184 dc_c30_1185 dc_c30_1186 dc_c30_1187 dc_c30_1188 dc_c30_1189 dc_c30_1190 dc_c30_1191 dc_c30_1192 dc_c30_1193 dc_c30_1194 dc_c30_1195 dc_c30_1196 dc_c30_1197 dc_c30_1198 dc_c30_1199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
