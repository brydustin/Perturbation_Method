theory OCX_c30_074
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1184: "oc_sub oc_b30 1184"
  by (oc_eval oc_c30_1184)

lemma oc_c30_1185: "oc_sub oc_b30 1185"
  by (oc_eval oc_c30_1185)

lemma oc_c30_1186: "oc_sub oc_b30 1186"
  by (oc_eval oc_c30_1186)

lemma oc_c30_1187: "oc_sub oc_b30 1187"
  by (oc_eval oc_c30_1187)

lemma oc_c30_1188: "oc_sub oc_b30 1188"
  by (oc_eval oc_c30_1188)

lemma oc_c30_1189: "oc_sub oc_b30 1189"
  by (oc_eval oc_c30_1189)

lemma oc_c30_1190: "oc_sub oc_b30 1190"
  by (oc_eval oc_c30_1190)

lemma oc_c30_1191: "oc_sub oc_b30 1191"
  by (oc_eval oc_c30_1191)

lemma oc_c30_1192: "oc_sub oc_b30 1192"
  by (oc_eval oc_c30_1192)

lemma oc_c30_1193: "oc_sub oc_b30 1193"
  by (oc_eval oc_c30_1193)

lemma oc_c30_1194: "oc_sub oc_b30 1194"
  by (oc_eval oc_c30_1194)

lemma oc_c30_1195: "oc_sub oc_b30 1195"
  by (oc_eval oc_c30_1195)

lemma oc_c30_1196: "oc_sub oc_b30 1196"
  by (oc_eval oc_c30_1196)

lemma oc_c30_1197: "oc_sub oc_b30 1197"
  by (oc_eval oc_c30_1197)

lemma oc_c30_1198: "oc_sub oc_b30 1198"
  by (oc_eval oc_c30_1198)

lemma oc_c30_1199: "oc_sub oc_b30 1199"
  by (oc_eval oc_c30_1199)

lemma upt_c30_074: "[1184..<1200] = [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]"
  by (simp add: upt_rec)

lemma sec_c30_074: "\<forall>j\<in>{16 * 74..<16 * 74 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 74..<16 * 74 + 16}"
  then have "j \<in> set [1184..<1200]" unfolding set_upt by simp
  then have "j \<in> set [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]" unfolding upt_c30_074 .
  then show "oc_sub oc_b30 j" using oc_c30_1184 oc_c30_1185 oc_c30_1186 oc_c30_1187 oc_c30_1188 oc_c30_1189 oc_c30_1190 oc_c30_1191 oc_c30_1192 oc_c30_1193 oc_c30_1194 oc_c30_1195 oc_c30_1196 oc_c30_1197 oc_c30_1198 oc_c30_1199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
