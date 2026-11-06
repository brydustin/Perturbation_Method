theory DCX_nc_078
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1248: "dc_sub None 1248"
  by (dc_eval dc_nc_1248)

lemma dc_nc_1249: "dc_sub None 1249"
  by (dc_eval dc_nc_1249)

lemma dc_nc_1250: "dc_sub None 1250"
  by (dc_eval dc_nc_1250)

lemma dc_nc_1251: "dc_sub None 1251"
  by (dc_eval dc_nc_1251)

lemma dc_nc_1252: "dc_sub None 1252"
  by (dc_eval dc_nc_1252)

lemma dc_nc_1253: "dc_sub None 1253"
  by (dc_eval dc_nc_1253)

lemma dc_nc_1254: "dc_sub None 1254"
  by (dc_eval dc_nc_1254)

lemma dc_nc_1255: "dc_sub None 1255"
  by (dc_eval dc_nc_1255)

lemma dc_nc_1256: "dc_sub None 1256"
  by (dc_eval dc_nc_1256)

lemma dc_nc_1257: "dc_sub None 1257"
  by (dc_eval dc_nc_1257)

lemma dc_nc_1258: "dc_sub None 1258"
  by (dc_eval dc_nc_1258)

lemma dc_nc_1259: "dc_sub None 1259"
  by (dc_eval dc_nc_1259)

lemma dc_nc_1260: "dc_sub None 1260"
  by (dc_eval dc_nc_1260)

lemma dc_nc_1261: "dc_sub None 1261"
  by (dc_eval dc_nc_1261)

lemma dc_nc_1262: "dc_sub None 1262"
  by (dc_eval dc_nc_1262)

lemma dc_nc_1263: "dc_sub None 1263"
  by (dc_eval dc_nc_1263)

lemma upt_nc_078: "[1248..<1264] = [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]"
  by (simp add: upt_rec)

lemma sec_nc_078: "\<forall>j\<in>{16 * 78..<16 * 78 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 78..<16 * 78 + 16}"
  then have "j \<in> set [1248..<1264]" unfolding set_upt by simp
  then have "j \<in> set [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]" unfolding upt_nc_078 .
  then show "dc_sub None j" using dc_nc_1248 dc_nc_1249 dc_nc_1250 dc_nc_1251 dc_nc_1252 dc_nc_1253 dc_nc_1254 dc_nc_1255 dc_nc_1256 dc_nc_1257 dc_nc_1258 dc_nc_1259 dc_nc_1260 dc_nc_1261 dc_nc_1262 dc_nc_1263
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
