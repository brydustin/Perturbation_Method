theory GDCX_nc_074
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1184: "gdc_sub None 1184"
  by (gdc_eval gdc_nc_1184)

lemma gdc_nc_1185: "gdc_sub None 1185"
  by (gdc_eval gdc_nc_1185)

lemma gdc_nc_1186: "gdc_sub None 1186"
  by (gdc_eval gdc_nc_1186)

lemma gdc_nc_1187: "gdc_sub None 1187"
  by (gdc_eval gdc_nc_1187)

lemma gdc_nc_1188: "gdc_sub None 1188"
  by (gdc_eval gdc_nc_1188)

lemma gdc_nc_1189: "gdc_sub None 1189"
  by (gdc_eval gdc_nc_1189)

lemma gdc_nc_1190: "gdc_sub None 1190"
  by (gdc_eval gdc_nc_1190)

lemma gdc_nc_1191: "gdc_sub None 1191"
  by (gdc_eval gdc_nc_1191)

lemma gdc_nc_1192: "gdc_sub None 1192"
  by (gdc_eval gdc_nc_1192)

lemma gdc_nc_1193: "gdc_sub None 1193"
  by (gdc_eval gdc_nc_1193)

lemma gdc_nc_1194: "gdc_sub None 1194"
  by (gdc_eval gdc_nc_1194)

lemma gdc_nc_1195: "gdc_sub None 1195"
  by (gdc_eval gdc_nc_1195)

lemma gdc_nc_1196: "gdc_sub None 1196"
  by (gdc_eval gdc_nc_1196)

lemma gdc_nc_1197: "gdc_sub None 1197"
  by (gdc_eval gdc_nc_1197)

lemma gdc_nc_1198: "gdc_sub None 1198"
  by (gdc_eval gdc_nc_1198)

lemma gdc_nc_1199: "gdc_sub None 1199"
  by (gdc_eval gdc_nc_1199)

lemma gupt_nc_074: "[1184..<1200] = [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]"
  by (simp add: upt_rec)

lemma gsec_nc_074: "\<forall>j\<in>{16 * 74..<16 * 74 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 74..<16 * 74 + 16}"
  then have "j \<in> set [1184..<1200]" unfolding set_upt by simp
  then have "j \<in> set [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]" unfolding gupt_nc_074 .
  then show "gdc_sub None j" using gdc_nc_1184 gdc_nc_1185 gdc_nc_1186 gdc_nc_1187 gdc_nc_1188 gdc_nc_1189 gdc_nc_1190 gdc_nc_1191 gdc_nc_1192 gdc_nc_1193 gdc_nc_1194 gdc_nc_1195 gdc_nc_1196 gdc_nc_1197 gdc_nc_1198 gdc_nc_1199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
