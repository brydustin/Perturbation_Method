theory GOCX_nc_076
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1216: "goc_sub None 1216"
  by (goc_eval goc_nc_1216)

lemma goc_nc_1217: "goc_sub None 1217"
  by (goc_eval goc_nc_1217)

lemma goc_nc_1218: "goc_sub None 1218"
  by (goc_eval goc_nc_1218)

lemma goc_nc_1219: "goc_sub None 1219"
  by (goc_eval goc_nc_1219)

lemma goc_nc_1220: "goc_sub None 1220"
  by (goc_eval goc_nc_1220)

lemma goc_nc_1221: "goc_sub None 1221"
  by (goc_eval goc_nc_1221)

lemma goc_nc_1222: "goc_sub None 1222"
  by (goc_eval goc_nc_1222)

lemma goc_nc_1223: "goc_sub None 1223"
  by (goc_eval goc_nc_1223)

lemma goc_nc_1224: "goc_sub None 1224"
  by (goc_eval goc_nc_1224)

lemma goc_nc_1225: "goc_sub None 1225"
  by (goc_eval goc_nc_1225)

lemma goc_nc_1226: "goc_sub None 1226"
  by (goc_eval goc_nc_1226)

lemma goc_nc_1227: "goc_sub None 1227"
  by (goc_eval goc_nc_1227)

lemma goc_nc_1228: "goc_sub None 1228"
  by (goc_eval goc_nc_1228)

lemma goc_nc_1229: "goc_sub None 1229"
  by (goc_eval goc_nc_1229)

lemma goc_nc_1230: "goc_sub None 1230"
  by (goc_eval goc_nc_1230)

lemma goc_nc_1231: "goc_sub None 1231"
  by (goc_eval goc_nc_1231)

lemma gupt_nc_076: "[1216..<1232] = [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]"
  by (simp add: upt_rec)

lemma gsec_nc_076: "\<forall>j\<in>{16 * 76..<16 * 76 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 76..<16 * 76 + 16}"
  then have "j \<in> set [1216..<1232]" unfolding set_upt by simp
  then have "j \<in> set [1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231]" unfolding gupt_nc_076 .
  then show "goc_sub None j" using goc_nc_1216 goc_nc_1217 goc_nc_1218 goc_nc_1219 goc_nc_1220 goc_nc_1221 goc_nc_1222 goc_nc_1223 goc_nc_1224 goc_nc_1225 goc_nc_1226 goc_nc_1227 goc_nc_1228 goc_nc_1229 goc_nc_1230 goc_nc_1231
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
