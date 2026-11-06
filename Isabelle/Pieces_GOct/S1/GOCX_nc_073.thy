theory GOCX_nc_073
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1168: "goc_sub None 1168"
  by (goc_eval goc_nc_1168)

lemma goc_nc_1169: "goc_sub None 1169"
  by (goc_eval goc_nc_1169)

lemma goc_nc_1170: "goc_sub None 1170"
  by (goc_eval goc_nc_1170)

lemma goc_nc_1171: "goc_sub None 1171"
  by (goc_eval goc_nc_1171)

lemma goc_nc_1172: "goc_sub None 1172"
  by (goc_eval goc_nc_1172)

lemma goc_nc_1173: "goc_sub None 1173"
  by (goc_eval goc_nc_1173)

lemma goc_nc_1174: "goc_sub None 1174"
  by (goc_eval goc_nc_1174)

lemma goc_nc_1175: "goc_sub None 1175"
  by (goc_eval goc_nc_1175)

lemma goc_nc_1176: "goc_sub None 1176"
  by (goc_eval goc_nc_1176)

lemma goc_nc_1177: "goc_sub None 1177"
  by (goc_eval goc_nc_1177)

lemma goc_nc_1178: "goc_sub None 1178"
  by (goc_eval goc_nc_1178)

lemma goc_nc_1179: "goc_sub None 1179"
  by (goc_eval goc_nc_1179)

lemma goc_nc_1180: "goc_sub None 1180"
  by (goc_eval goc_nc_1180)

lemma goc_nc_1181: "goc_sub None 1181"
  by (goc_eval goc_nc_1181)

lemma goc_nc_1182: "goc_sub None 1182"
  by (goc_eval goc_nc_1182)

lemma goc_nc_1183: "goc_sub None 1183"
  by (goc_eval goc_nc_1183)

lemma gupt_nc_073: "[1168..<1184] = [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]"
  by (simp add: upt_rec)

lemma gsec_nc_073: "\<forall>j\<in>{16 * 73..<16 * 73 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 73..<16 * 73 + 16}"
  then have "j \<in> set [1168..<1184]" unfolding set_upt by simp
  then have "j \<in> set [1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183]" unfolding gupt_nc_073 .
  then show "goc_sub None j" using goc_nc_1168 goc_nc_1169 goc_nc_1170 goc_nc_1171 goc_nc_1172 goc_nc_1173 goc_nc_1174 goc_nc_1175 goc_nc_1176 goc_nc_1177 goc_nc_1178 goc_nc_1179 goc_nc_1180 goc_nc_1181 goc_nc_1182 goc_nc_1183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
