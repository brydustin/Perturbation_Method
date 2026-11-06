theory DCX_nc_074
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1184: "dc_sub None 1184"
  by (dc_eval dc_nc_1184)

lemma dc_nc_1185: "dc_sub None 1185"
  by (dc_eval dc_nc_1185)

lemma dc_nc_1186: "dc_sub None 1186"
  by (dc_eval dc_nc_1186)

lemma dc_nc_1187: "dc_sub None 1187"
  by (dc_eval dc_nc_1187)

lemma dc_nc_1188: "dc_sub None 1188"
  by (dc_eval dc_nc_1188)

lemma dc_nc_1189: "dc_sub None 1189"
  by (dc_eval dc_nc_1189)

lemma dc_nc_1190: "dc_sub None 1190"
  by (dc_eval dc_nc_1190)

lemma dc_nc_1191: "dc_sub None 1191"
  by (dc_eval dc_nc_1191)

lemma dc_nc_1192: "dc_sub None 1192"
  by (dc_eval dc_nc_1192)

lemma dc_nc_1193: "dc_sub None 1193"
  by (dc_eval dc_nc_1193)

lemma dc_nc_1194: "dc_sub None 1194"
  by (dc_eval dc_nc_1194)

lemma dc_nc_1195: "dc_sub None 1195"
  by (dc_eval dc_nc_1195)

lemma dc_nc_1196: "dc_sub None 1196"
  by (dc_eval dc_nc_1196)

lemma dc_nc_1197: "dc_sub None 1197"
  by (dc_eval dc_nc_1197)

lemma dc_nc_1198: "dc_sub None 1198"
  by (dc_eval dc_nc_1198)

lemma dc_nc_1199: "dc_sub None 1199"
  by (dc_eval dc_nc_1199)

lemma upt_nc_074: "[1184..<1200] = [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]"
  by (simp add: upt_rec)

lemma sec_nc_074: "\<forall>j\<in>{16 * 74..<16 * 74 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 74..<16 * 74 + 16}"
  then have "j \<in> set [1184..<1200]" unfolding set_upt by simp
  then have "j \<in> set [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]" unfolding upt_nc_074 .
  then show "dc_sub None j" using dc_nc_1184 dc_nc_1185 dc_nc_1186 dc_nc_1187 dc_nc_1188 dc_nc_1189 dc_nc_1190 dc_nc_1191 dc_nc_1192 dc_nc_1193 dc_nc_1194 dc_nc_1195 dc_nc_1196 dc_nc_1197 dc_nc_1198 dc_nc_1199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
