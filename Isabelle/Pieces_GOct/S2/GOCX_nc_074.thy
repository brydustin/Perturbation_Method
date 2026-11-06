theory GOCX_nc_074
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1184: "goc_sub None 1184"
  by (goc_eval goc_nc_1184)

lemma goc_nc_1185: "goc_sub None 1185"
  by (goc_eval goc_nc_1185)

lemma goc_nc_1186: "goc_sub None 1186"
  by (goc_eval goc_nc_1186)

lemma goc_nc_1187: "goc_sub None 1187"
  by (goc_eval goc_nc_1187)

lemma goc_nc_1188: "goc_sub None 1188"
  by (goc_eval goc_nc_1188)

lemma goc_nc_1189: "goc_sub None 1189"
  by (goc_eval goc_nc_1189)

lemma goc_nc_1190: "goc_sub None 1190"
  by (goc_eval goc_nc_1190)

lemma goc_nc_1191: "goc_sub None 1191"
  by (goc_eval goc_nc_1191)

lemma goc_nc_1192: "goc_sub None 1192"
  by (goc_eval goc_nc_1192)

lemma goc_nc_1193: "goc_sub None 1193"
  by (goc_eval goc_nc_1193)

lemma goc_nc_1194: "goc_sub None 1194"
  by (goc_eval goc_nc_1194)

lemma goc_nc_1195: "goc_sub None 1195"
  by (goc_eval goc_nc_1195)

lemma goc_nc_1196: "goc_sub None 1196"
  by (goc_eval goc_nc_1196)

lemma goc_nc_1197: "goc_sub None 1197"
  by (goc_eval goc_nc_1197)

lemma goc_nc_1198: "goc_sub None 1198"
  by (goc_eval goc_nc_1198)

lemma goc_nc_1199: "goc_sub None 1199"
  by (goc_eval goc_nc_1199)

lemma gupt_nc_074: "[1184..<1200] = [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]"
  by (simp add: upt_rec)

lemma gsec_nc_074: "\<forall>j\<in>{16 * 74..<16 * 74 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 74..<16 * 74 + 16}"
  then have "j \<in> set [1184..<1200]" unfolding set_upt by simp
  then have "j \<in> set [1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199]" unfolding gupt_nc_074 .
  then show "goc_sub None j" using goc_nc_1184 goc_nc_1185 goc_nc_1186 goc_nc_1187 goc_nc_1188 goc_nc_1189 goc_nc_1190 goc_nc_1191 goc_nc_1192 goc_nc_1193 goc_nc_1194 goc_nc_1195 goc_nc_1196 goc_nc_1197 goc_nc_1198 goc_nc_1199
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
