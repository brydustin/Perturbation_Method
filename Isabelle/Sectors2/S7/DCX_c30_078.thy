theory DCX_c30_078
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1248: "dc_sub dc_b30 1248"
  by (dc_eval dc_c30_1248)

lemma dc_c30_1249: "dc_sub dc_b30 1249"
  by (dc_eval dc_c30_1249)

lemma dc_c30_1250: "dc_sub dc_b30 1250"
  by (dc_eval dc_c30_1250)

lemma dc_c30_1251: "dc_sub dc_b30 1251"
  by (dc_eval dc_c30_1251)

lemma dc_c30_1252: "dc_sub dc_b30 1252"
  by (dc_eval dc_c30_1252)

lemma dc_c30_1253: "dc_sub dc_b30 1253"
  by (dc_eval dc_c30_1253)

lemma dc_c30_1254: "dc_sub dc_b30 1254"
  by (dc_eval dc_c30_1254)

lemma dc_c30_1255: "dc_sub dc_b30 1255"
  by (dc_eval dc_c30_1255)

lemma dc_c30_1256: "dc_sub dc_b30 1256"
  by (dc_eval dc_c30_1256)

lemma dc_c30_1257: "dc_sub dc_b30 1257"
  by (dc_eval dc_c30_1257)

lemma dc_c30_1258: "dc_sub dc_b30 1258"
  by (dc_eval dc_c30_1258)

lemma dc_c30_1259: "dc_sub dc_b30 1259"
  by (dc_eval dc_c30_1259)

lemma dc_c30_1260: "dc_sub dc_b30 1260"
  by (dc_eval dc_c30_1260)

lemma dc_c30_1261: "dc_sub dc_b30 1261"
  by (dc_eval dc_c30_1261)

lemma dc_c30_1262: "dc_sub dc_b30 1262"
  by (dc_eval dc_c30_1262)

lemma dc_c30_1263: "dc_sub dc_b30 1263"
  by (dc_eval dc_c30_1263)

lemma upt_c30_078: "[1248..<1264] = [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]"
  by (simp add: upt_rec)

lemma sec_c30_078: "\<forall>j\<in>{16 * 78..<16 * 78 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 78..<16 * 78 + 16}"
  then have "j \<in> set [1248..<1264]" unfolding set_upt by simp
  then have "j \<in> set [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]" unfolding upt_c30_078 .
  then show "dc_sub dc_b30 j" using dc_c30_1248 dc_c30_1249 dc_c30_1250 dc_c30_1251 dc_c30_1252 dc_c30_1253 dc_c30_1254 dc_c30_1255 dc_c30_1256 dc_c30_1257 dc_c30_1258 dc_c30_1259 dc_c30_1260 dc_c30_1261 dc_c30_1262 dc_c30_1263
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
