theory DCX_nc_073
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1168: "dc_sub None 1168"
  by (dc_eval dc_nc_1168)

lemma dc_nc_1169: "dc_sub None 1169"
  by (dc_eval dc_nc_1169)

lemma dc_nc_1170: "dc_sub None 1170"
  by (dc_eval dc_nc_1170)

lemma dc_nc_1171: "dc_sub None 1171"
  by (dc_eval dc_nc_1171)

lemma dc_nc_1172: "dc_sub None 1172"
  by (dc_eval dc_nc_1172)

lemma dc_nc_1173: "dc_sub None 1173"
  by (dc_eval dc_nc_1173)

lemma dc_nc_1174: "dc_sub None 1174"
  by (dc_eval dc_nc_1174)

lemma dc_nc_1175: "dc_sub None 1175"
  by (dc_eval dc_nc_1175)

lemma dc_nc_1176: "dc_sub None 1176"
  by (dc_eval dc_nc_1176)

lemma dc_nc_1177: "dc_sub None 1177"
  by (dc_eval dc_nc_1177)

lemma dc_nc_1178: "dc_sub None 1178"
  by (dc_eval dc_nc_1178)

lemma dc_nc_1179: "dc_sub None 1179"
  by (dc_eval dc_nc_1179)

lemma dc_nc_1180: "dc_sub None 1180"
  by (dc_eval dc_nc_1180)

lemma dc_nc_1181: "dc_sub None 1181"
  by (dc_eval dc_nc_1181)

lemma dc_nc_1182: "dc_sub None 1182"
  by (dc_eval dc_nc_1182)

lemma dc_nc_1183: "dc_sub None 1183"
  by (dc_eval dc_nc_1183)

lemma upt_nc_073: "[1168..<1184] = [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]"
  by (simp add: upt_rec)

lemma sec_nc_073: "\<forall>j\<in>{16 * 73..<16 * 73 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 73..<16 * 73 + 16}"
  then have "j \<in> set [1168..<1184]" unfolding set_upt by simp
  then have "j \<in> set [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]" unfolding upt_nc_073 .
  then show "dc_sub None j" using dc_nc_1168 dc_nc_1169 dc_nc_1170 dc_nc_1171 dc_nc_1172 dc_nc_1173 dc_nc_1174 dc_nc_1175 dc_nc_1176 dc_nc_1177 dc_nc_1178 dc_nc_1179 dc_nc_1180 dc_nc_1181 dc_nc_1182 dc_nc_1183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
