theory GDCX_nc_078
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1248: "gdc_sub None 1248"
  by (gdc_eval gdc_nc_1248)

lemma gdc_nc_1249: "gdc_sub None 1249"
  by (gdc_eval gdc_nc_1249)

lemma gdc_nc_1250: "gdc_sub None 1250"
  by (gdc_eval gdc_nc_1250)

lemma gdc_nc_1251: "gdc_sub None 1251"
  by (gdc_eval gdc_nc_1251)

lemma gdc_nc_1252: "gdc_sub None 1252"
  by (gdc_eval gdc_nc_1252)

lemma gdc_nc_1253: "gdc_sub None 1253"
  by (gdc_eval gdc_nc_1253)

lemma gdc_nc_1254: "gdc_sub None 1254"
  by (gdc_eval gdc_nc_1254)

lemma gdc_nc_1255: "gdc_sub None 1255"
  by (gdc_eval gdc_nc_1255)

lemma gdc_nc_1256: "gdc_sub None 1256"
  by (gdc_eval gdc_nc_1256)

lemma gdc_nc_1257: "gdc_sub None 1257"
  by (gdc_eval gdc_nc_1257)

lemma gdc_nc_1258: "gdc_sub None 1258"
  by (gdc_eval gdc_nc_1258)

lemma gdc_nc_1259: "gdc_sub None 1259"
  by (gdc_eval gdc_nc_1259)

lemma gdc_nc_1260: "gdc_sub None 1260"
  by (gdc_eval gdc_nc_1260)

lemma gdc_nc_1261: "gdc_sub None 1261"
  by (gdc_eval gdc_nc_1261)

lemma gdc_nc_1262: "gdc_sub None 1262"
  by (gdc_eval gdc_nc_1262)

lemma gdc_nc_1263: "gdc_sub None 1263"
  by (gdc_eval gdc_nc_1263)

lemma gupt_nc_078: "[1248..<1264] = [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]"
  by (simp add: upt_rec)

lemma gsec_nc_078: "\<forall>j\<in>{16 * 78..<16 * 78 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 78..<16 * 78 + 16}"
  then have "j \<in> set [1248..<1264]" unfolding set_upt by simp
  then have "j \<in> set [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]" unfolding gupt_nc_078 .
  then show "gdc_sub None j" using gdc_nc_1248 gdc_nc_1249 gdc_nc_1250 gdc_nc_1251 gdc_nc_1252 gdc_nc_1253 gdc_nc_1254 gdc_nc_1255 gdc_nc_1256 gdc_nc_1257 gdc_nc_1258 gdc_nc_1259 gdc_nc_1260 gdc_nc_1261 gdc_nc_1262 gdc_nc_1263
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
