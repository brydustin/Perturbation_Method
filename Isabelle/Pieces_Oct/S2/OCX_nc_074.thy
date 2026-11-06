theory OCX_nc_074
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1184: "oc_sub None 1184"
  by (oc_eval oc_nc_1184)

lemma oc_nc_1185: "oc_sub None 1185"
  by (oc_eval oc_nc_1185)

lemma oc_nc_1186: "oc_sub None 1186"
  by (oc_eval oc_nc_1186)

lemma oc_nc_1187: "oc_sub None 1187"
  by (oc_eval oc_nc_1187)

lemma oc_nc_1188: "oc_sub None 1188"
  by (oc_eval oc_nc_1188)

lemma oc_nc_1189: "oc_sub None 1189"
  by (oc_eval oc_nc_1189)

lemma oc_nc_1190: "oc_sub None 1190"
  by (oc_eval oc_nc_1190)

lemma oc_nc_1191: "oc_sub None 1191"
  by (oc_eval oc_nc_1191)

lemma oc_nc_1192: "oc_sub None 1192"
  by (oc_eval oc_nc_1192)

lemma oc_nc_1193: "oc_sub None 1193"
  by (oc_eval oc_nc_1193)

lemma oc_nc_1194: "oc_sub None 1194"
  by (oc_eval oc_nc_1194)

lemma oc_nc_1195: "oc_sub None 1195"
  by (oc_eval oc_nc_1195)

lemma oc_nc_1196: "oc_sub None 1196"
  by (oc_eval oc_nc_1196)

lemma oc_nc_1197: "oc_sub None 1197"
  by (oc_eval oc_nc_1197)

lemma oc_nc_1198: "oc_sub None 1198"
  by (oc_eval oc_nc_1198)

lemma oc_nc_1199: "oc_sub None 1199"
  by (oc_eval oc_nc_1199)

lemma upt_nc_074: "[1184..<1200] = [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]"
  by (simp add: upt_rec)

lemma sec_nc_074: "\<forall>j\<in>{16 * 74..<16 * 74 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 74..<16 * 74 + 16}"
  then have "j \<in> set [1184..<1200]" unfolding set_upt by simp
  then have "j \<in> set [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]" unfolding upt_nc_074 .
  then show "oc_sub None j" using oc_nc_1184 oc_nc_1185 oc_nc_1186 oc_nc_1187 oc_nc_1188 oc_nc_1189 oc_nc_1190 oc_nc_1191 oc_nc_1192 oc_nc_1193 oc_nc_1194 oc_nc_1195 oc_nc_1196 oc_nc_1197 oc_nc_1198 oc_nc_1199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
