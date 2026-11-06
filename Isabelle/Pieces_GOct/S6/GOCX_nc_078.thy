theory GOCX_nc_078
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1248: "goc_sub None 1248"
  by (goc_eval goc_nc_1248)

lemma goc_nc_1249: "goc_sub None 1249"
  by (goc_eval goc_nc_1249)

lemma goc_nc_1250: "goc_sub None 1250"
  by (goc_eval goc_nc_1250)

lemma goc_nc_1251: "goc_sub None 1251"
  by (goc_eval goc_nc_1251)

lemma goc_nc_1252: "goc_sub None 1252"
  by (goc_eval goc_nc_1252)

lemma goc_nc_1253: "goc_sub None 1253"
  by (goc_eval goc_nc_1253)

lemma goc_nc_1254: "goc_sub None 1254"
  by (goc_eval goc_nc_1254)

lemma goc_nc_1255: "goc_sub None 1255"
  by (goc_eval goc_nc_1255)

lemma goc_nc_1256: "goc_sub None 1256"
  by (goc_eval goc_nc_1256)

lemma goc_nc_1257: "goc_sub None 1257"
  by (goc_eval goc_nc_1257)

lemma goc_nc_1258: "goc_sub None 1258"
  by (goc_eval goc_nc_1258)

lemma goc_nc_1259: "goc_sub None 1259"
  by (goc_eval goc_nc_1259)

lemma goc_nc_1260: "goc_sub None 1260"
  by (goc_eval goc_nc_1260)

lemma goc_nc_1261: "goc_sub None 1261"
  by (goc_eval goc_nc_1261)

lemma goc_nc_1262: "goc_sub None 1262"
  by (goc_eval goc_nc_1262)

lemma goc_nc_1263: "goc_sub None 1263"
  by (goc_eval goc_nc_1263)

lemma gupt_nc_078: "[1248..<1264] = [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]"
  by (simp add: upt_rec)

lemma gsec_nc_078: "\<forall>j\<in>{16 * 78..<16 * 78 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 78..<16 * 78 + 16}"
  then have "j \<in> set [1248..<1264]" unfolding set_upt by simp
  then have "j \<in> set [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]" unfolding gupt_nc_078 .
  then show "goc_sub None j" using goc_nc_1248 goc_nc_1249 goc_nc_1250 goc_nc_1251 goc_nc_1252 goc_nc_1253 goc_nc_1254 goc_nc_1255 goc_nc_1256 goc_nc_1257 goc_nc_1258 goc_nc_1259 goc_nc_1260 goc_nc_1261 goc_nc_1262 goc_nc_1263
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
