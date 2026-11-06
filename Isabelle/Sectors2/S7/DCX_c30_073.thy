theory DCX_c30_073
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1168: "dc_sub dc_b30 1168"
  by (dc_eval dc_c30_1168)

lemma dc_c30_1169: "dc_sub dc_b30 1169"
  by (dc_eval dc_c30_1169)

lemma dc_c30_1170: "dc_sub dc_b30 1170"
  by (dc_eval dc_c30_1170)

lemma dc_c30_1171: "dc_sub dc_b30 1171"
  by (dc_eval dc_c30_1171)

lemma dc_c30_1172: "dc_sub dc_b30 1172"
  by (dc_eval dc_c30_1172)

lemma dc_c30_1173: "dc_sub dc_b30 1173"
  by (dc_eval dc_c30_1173)

lemma dc_c30_1174: "dc_sub dc_b30 1174"
  by (dc_eval dc_c30_1174)

lemma dc_c30_1175: "dc_sub dc_b30 1175"
  by (dc_eval dc_c30_1175)

lemma dc_c30_1176: "dc_sub dc_b30 1176"
  by (dc_eval dc_c30_1176)

lemma dc_c30_1177: "dc_sub dc_b30 1177"
  by (dc_eval dc_c30_1177)

lemma dc_c30_1178: "dc_sub dc_b30 1178"
  by (dc_eval dc_c30_1178)

lemma dc_c30_1179: "dc_sub dc_b30 1179"
  by (dc_eval dc_c30_1179)

lemma dc_c30_1180: "dc_sub dc_b30 1180"
  by (dc_eval dc_c30_1180)

lemma dc_c30_1181: "dc_sub dc_b30 1181"
  by (dc_eval dc_c30_1181)

lemma dc_c30_1182: "dc_sub dc_b30 1182"
  by (dc_eval dc_c30_1182)

lemma dc_c30_1183: "dc_sub dc_b30 1183"
  by (dc_eval dc_c30_1183)

lemma upt_c30_073: "[1168..<1184] = [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]"
  by (simp add: upt_rec)

lemma sec_c30_073: "\<forall>j\<in>{16 * 73..<16 * 73 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 73..<16 * 73 + 16}"
  then have "j \<in> set [1168..<1184]" unfolding set_upt by simp
  then have "j \<in> set [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]" unfolding upt_c30_073 .
  then show "dc_sub dc_b30 j" using dc_c30_1168 dc_c30_1169 dc_c30_1170 dc_c30_1171 dc_c30_1172 dc_c30_1173 dc_c30_1174 dc_c30_1175 dc_c30_1176 dc_c30_1177 dc_c30_1178 dc_c30_1179 dc_c30_1180 dc_c30_1181 dc_c30_1182 dc_c30_1183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
