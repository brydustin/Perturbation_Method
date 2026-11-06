theory OCX_nc_078
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1248: "oc_sub None 1248"
  by (oc_eval oc_nc_1248)

lemma oc_nc_1249: "oc_sub None 1249"
  by (oc_eval oc_nc_1249)

lemma oc_nc_1250: "oc_sub None 1250"
  by (oc_eval oc_nc_1250)

lemma oc_nc_1251: "oc_sub None 1251"
  by (oc_eval oc_nc_1251)

lemma oc_nc_1252: "oc_sub None 1252"
  by (oc_eval oc_nc_1252)

lemma oc_nc_1253: "oc_sub None 1253"
  by (oc_eval oc_nc_1253)

lemma oc_nc_1254: "oc_sub None 1254"
  by (oc_eval oc_nc_1254)

lemma oc_nc_1255: "oc_sub None 1255"
  by (oc_eval oc_nc_1255)

lemma oc_nc_1256: "oc_sub None 1256"
  by (oc_eval oc_nc_1256)

lemma oc_nc_1257: "oc_sub None 1257"
  by (oc_eval oc_nc_1257)

lemma oc_nc_1258: "oc_sub None 1258"
  by (oc_eval oc_nc_1258)

lemma oc_nc_1259: "oc_sub None 1259"
  by (oc_eval oc_nc_1259)

lemma oc_nc_1260: "oc_sub None 1260"
  by (oc_eval oc_nc_1260)

lemma oc_nc_1261: "oc_sub None 1261"
  by (oc_eval oc_nc_1261)

lemma oc_nc_1262: "oc_sub None 1262"
  by (oc_eval oc_nc_1262)

lemma oc_nc_1263: "oc_sub None 1263"
  by (oc_eval oc_nc_1263)

lemma upt_nc_078: "[1248..<1264] = [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]"
  by (simp add: upt_rec)

lemma sec_nc_078: "\<forall>j\<in>{16 * 78..<16 * 78 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 78..<16 * 78 + 16}"
  then have "j \<in> set [1248..<1264]" unfolding set_upt by simp
  then have "j \<in> set [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]" unfolding upt_nc_078 .
  then show "oc_sub None j" using oc_nc_1248 oc_nc_1249 oc_nc_1250 oc_nc_1251 oc_nc_1252 oc_nc_1253 oc_nc_1254 oc_nc_1255 oc_nc_1256 oc_nc_1257 oc_nc_1258 oc_nc_1259 oc_nc_1260 oc_nc_1261 oc_nc_1262 oc_nc_1263
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
