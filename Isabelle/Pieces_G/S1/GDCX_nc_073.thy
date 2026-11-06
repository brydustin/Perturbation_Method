theory GDCX_nc_073
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1168: "gdc_sub None 1168"
  by (gdc_eval gdc_nc_1168)

lemma gdc_nc_1169: "gdc_sub None 1169"
  by (gdc_eval gdc_nc_1169)

lemma gdc_nc_1170: "gdc_sub None 1170"
  by (gdc_eval gdc_nc_1170)

lemma gdc_nc_1171: "gdc_sub None 1171"
  by (gdc_eval gdc_nc_1171)

lemma gdc_nc_1172: "gdc_sub None 1172"
  by (gdc_eval gdc_nc_1172)

lemma gdc_nc_1173: "gdc_sub None 1173"
  by (gdc_eval gdc_nc_1173)

lemma gdc_nc_1174: "gdc_sub None 1174"
  by (gdc_eval gdc_nc_1174)

lemma gdc_nc_1175: "gdc_sub None 1175"
  by (gdc_eval gdc_nc_1175)

lemma gdc_nc_1176: "gdc_sub None 1176"
  by (gdc_eval gdc_nc_1176)

lemma gdc_nc_1177: "gdc_sub None 1177"
  by (gdc_eval gdc_nc_1177)

lemma gdc_nc_1178: "gdc_sub None 1178"
  by (gdc_eval gdc_nc_1178)

lemma gdc_nc_1179: "gdc_sub None 1179"
  by (gdc_eval gdc_nc_1179)

lemma gdc_nc_1180: "gdc_sub None 1180"
  by (gdc_eval gdc_nc_1180)

lemma gdc_nc_1181: "gdc_sub None 1181"
  by (gdc_eval gdc_nc_1181)

lemma gdc_nc_1182: "gdc_sub None 1182"
  by (gdc_eval gdc_nc_1182)

lemma gdc_nc_1183: "gdc_sub None 1183"
  by (gdc_eval gdc_nc_1183)

lemma gupt_nc_073: "[1168..<1184] = [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]"
  by (simp add: upt_rec)

lemma gsec_nc_073: "\<forall>j\<in>{16 * 73..<16 * 73 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 73..<16 * 73 + 16}"
  then have "j \<in> set [1168..<1184]" unfolding set_upt by simp
  then have "j \<in> set [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]" unfolding gupt_nc_073 .
  then show "gdc_sub None j" using gdc_nc_1168 gdc_nc_1169 gdc_nc_1170 gdc_nc_1171 gdc_nc_1172 gdc_nc_1173 gdc_nc_1174 gdc_nc_1175 gdc_nc_1176 gdc_nc_1177 gdc_nc_1178 gdc_nc_1179 gdc_nc_1180 gdc_nc_1181 gdc_nc_1182 gdc_nc_1183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
