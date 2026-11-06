theory OCX_c30_078
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1248: "oc_sub oc_b30 1248"
  by (oc_eval oc_c30_1248)

lemma oc_c30_1249: "oc_sub oc_b30 1249"
  by (oc_eval oc_c30_1249)

lemma oc_c30_1250: "oc_sub oc_b30 1250"
  by (oc_eval oc_c30_1250)

lemma oc_c30_1251: "oc_sub oc_b30 1251"
  by (oc_eval oc_c30_1251)

lemma oc_c30_1252: "oc_sub oc_b30 1252"
  by (oc_eval oc_c30_1252)

lemma oc_c30_1253: "oc_sub oc_b30 1253"
  by (oc_eval oc_c30_1253)

lemma oc_c30_1254: "oc_sub oc_b30 1254"
  by (oc_eval oc_c30_1254)

lemma oc_c30_1255: "oc_sub oc_b30 1255"
  by (oc_eval oc_c30_1255)

lemma oc_c30_1256: "oc_sub oc_b30 1256"
  by (oc_eval oc_c30_1256)

lemma oc_c30_1257: "oc_sub oc_b30 1257"
  by (oc_eval oc_c30_1257)

lemma oc_c30_1258: "oc_sub oc_b30 1258"
  by (oc_eval oc_c30_1258)

lemma oc_c30_1259: "oc_sub oc_b30 1259"
  by (oc_eval oc_c30_1259)

lemma oc_c30_1260: "oc_sub oc_b30 1260"
  by (oc_eval oc_c30_1260)

lemma oc_c30_1261: "oc_sub oc_b30 1261"
  by (oc_eval oc_c30_1261)

lemma oc_c30_1262: "oc_sub oc_b30 1262"
  by (oc_eval oc_c30_1262)

lemma oc_c30_1263: "oc_sub oc_b30 1263"
  by (oc_eval oc_c30_1263)

lemma upt_c30_078: "[1248..<1264] = [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]"
  by (simp add: upt_rec)

lemma sec_c30_078: "\<forall>j\<in>{16 * 78..<16 * 78 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 78..<16 * 78 + 16}"
  then have "j \<in> set [1248..<1264]" unfolding set_upt by simp
  then have "j \<in> set [1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263]" unfolding upt_c30_078 .
  then show "oc_sub oc_b30 j" using oc_c30_1248 oc_c30_1249 oc_c30_1250 oc_c30_1251 oc_c30_1252 oc_c30_1253 oc_c30_1254 oc_c30_1255 oc_c30_1256 oc_c30_1257 oc_c30_1258 oc_c30_1259 oc_c30_1260 oc_c30_1261 oc_c30_1262 oc_c30_1263
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
