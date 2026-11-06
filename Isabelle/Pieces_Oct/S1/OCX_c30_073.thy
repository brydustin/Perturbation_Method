theory OCX_c30_073
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1168: "oc_sub oc_b30 1168"
  by (oc_eval oc_c30_1168)

lemma oc_c30_1169: "oc_sub oc_b30 1169"
  by (oc_eval oc_c30_1169)

lemma oc_c30_1170: "oc_sub oc_b30 1170"
  by (oc_eval oc_c30_1170)

lemma oc_c30_1171: "oc_sub oc_b30 1171"
  by (oc_eval oc_c30_1171)

lemma oc_c30_1172: "oc_sub oc_b30 1172"
  by (oc_eval oc_c30_1172)

lemma oc_c30_1173: "oc_sub oc_b30 1173"
  by (oc_eval oc_c30_1173)

lemma oc_c30_1174: "oc_sub oc_b30 1174"
  by (oc_eval oc_c30_1174)

lemma oc_c30_1175: "oc_sub oc_b30 1175"
  by (oc_eval oc_c30_1175)

lemma oc_c30_1176: "oc_sub oc_b30 1176"
  by (oc_eval oc_c30_1176)

lemma oc_c30_1177: "oc_sub oc_b30 1177"
  by (oc_eval oc_c30_1177)

lemma oc_c30_1178: "oc_sub oc_b30 1178"
  by (oc_eval oc_c30_1178)

lemma oc_c30_1179: "oc_sub oc_b30 1179"
  by (oc_eval oc_c30_1179)

lemma oc_c30_1180: "oc_sub oc_b30 1180"
  by (oc_eval oc_c30_1180)

lemma oc_c30_1181: "oc_sub oc_b30 1181"
  by (oc_eval oc_c30_1181)

lemma oc_c30_1182: "oc_sub oc_b30 1182"
  by (oc_eval oc_c30_1182)

lemma oc_c30_1183: "oc_sub oc_b30 1183"
  by (oc_eval oc_c30_1183)

lemma upt_c30_073: "[1168..<1184] = [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]"
  by (simp add: upt_rec)

lemma sec_c30_073: "\<forall>j\<in>{16 * 73..<16 * 73 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 73..<16 * 73 + 16}"
  then have "j \<in> set [1168..<1184]" unfolding set_upt by simp
  then have "j \<in> set [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]" unfolding upt_c30_073 .
  then show "oc_sub oc_b30 j" using oc_c30_1168 oc_c30_1169 oc_c30_1170 oc_c30_1171 oc_c30_1172 oc_c30_1173 oc_c30_1174 oc_c30_1175 oc_c30_1176 oc_c30_1177 oc_c30_1178 oc_c30_1179 oc_c30_1180 oc_c30_1181 oc_c30_1182 oc_c30_1183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
