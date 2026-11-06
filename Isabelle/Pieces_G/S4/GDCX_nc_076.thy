theory GDCX_nc_076
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1216: "gdc_sub None 1216"
  by (gdc_eval gdc_nc_1216)

lemma gdc_nc_1217: "gdc_sub None 1217"
  by (gdc_eval gdc_nc_1217)

lemma gdc_nc_1218: "gdc_sub None 1218"
  by (gdc_eval gdc_nc_1218)

lemma gdc_nc_1219: "gdc_sub None 1219"
  by (gdc_eval gdc_nc_1219)

lemma gdc_nc_1220: "gdc_sub None 1220"
  by (gdc_eval gdc_nc_1220)

lemma gdc_nc_1221: "gdc_sub None 1221"
  by (gdc_eval gdc_nc_1221)

lemma gdc_nc_1222: "gdc_sub None 1222"
  by (gdc_eval gdc_nc_1222)

lemma gdc_nc_1223: "gdc_sub None 1223"
  by (gdc_eval gdc_nc_1223)

lemma gdc_nc_1224: "gdc_sub None 1224"
  by (gdc_eval gdc_nc_1224)

lemma gdc_nc_1225: "gdc_sub None 1225"
  by (gdc_eval gdc_nc_1225)

lemma gdc_nc_1226: "gdc_sub None 1226"
  by (gdc_eval gdc_nc_1226)

lemma gdc_nc_1227: "gdc_sub None 1227"
  by (gdc_eval gdc_nc_1227)

lemma gdc_nc_1228: "gdc_sub None 1228"
  by (gdc_eval gdc_nc_1228)

lemma gdc_nc_1229: "gdc_sub None 1229"
  by (gdc_eval gdc_nc_1229)

lemma gdc_nc_1230: "gdc_sub None 1230"
  by (gdc_eval gdc_nc_1230)

lemma gdc_nc_1231: "gdc_sub None 1231"
  by (gdc_eval gdc_nc_1231)

lemma gupt_nc_076: "[1216..<1232] = [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]"
  by (simp add: upt_rec)

lemma gsec_nc_076: "\<forall>j\<in>{16 * 76..<16 * 76 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 76..<16 * 76 + 16}"
  then have "j \<in> set [1216..<1232]" unfolding set_upt by simp
  then have "j \<in> set [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]" unfolding gupt_nc_076 .
  then show "gdc_sub None j" using gdc_nc_1216 gdc_nc_1217 gdc_nc_1218 gdc_nc_1219 gdc_nc_1220 gdc_nc_1221 gdc_nc_1222 gdc_nc_1223 gdc_nc_1224 gdc_nc_1225 gdc_nc_1226 gdc_nc_1227 gdc_nc_1228 gdc_nc_1229 gdc_nc_1230 gdc_nc_1231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
