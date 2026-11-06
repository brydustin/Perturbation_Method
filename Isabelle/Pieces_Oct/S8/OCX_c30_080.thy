theory OCX_c30_080
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1280: "oc_sub oc_b30 1280"
  by (oc_eval oc_c30_1280)

lemma oc_c30_1281: "oc_sub oc_b30 1281"
  by (oc_eval oc_c30_1281)

lemma oc_c30_1282: "oc_sub oc_b30 1282"
  by (oc_eval oc_c30_1282)

lemma oc_c30_1283: "oc_sub oc_b30 1283"
  by (oc_eval oc_c30_1283)

lemma oc_c30_1284: "oc_sub oc_b30 1284"
  by (oc_eval oc_c30_1284)

lemma oc_c30_1285: "oc_sub oc_b30 1285"
  by (oc_eval oc_c30_1285)

lemma oc_c30_1286: "oc_sub oc_b30 1286"
  by (oc_eval oc_c30_1286)

lemma oc_c30_1287: "oc_sub oc_b30 1287"
  by (oc_eval oc_c30_1287)

lemma oc_c30_1288: "oc_sub oc_b30 1288"
  by (oc_eval oc_c30_1288)

lemma oc_c30_1289: "oc_sub oc_b30 1289"
  by (oc_eval oc_c30_1289)

lemma oc_c30_1290: "oc_sub oc_b30 1290"
  by (oc_eval oc_c30_1290)

lemma oc_c30_1291: "oc_sub oc_b30 1291"
  by (oc_eval oc_c30_1291)

lemma oc_c30_1292: "oc_sub oc_b30 1292"
  by (oc_eval oc_c30_1292)

lemma oc_c30_1293: "oc_sub oc_b30 1293"
  by (oc_eval oc_c30_1293)

lemma oc_c30_1294: "oc_sub oc_b30 1294"
  by (oc_eval oc_c30_1294)

lemma oc_c30_1295: "oc_sub oc_b30 1295"
  by (oc_eval oc_c30_1295)

lemma upt_c30_080: "[1280..<1296] = [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]"
  by (simp add: upt_rec)

lemma sec_c30_080: "\<forall>j\<in>{16 * 80..<16 * 80 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 80..<16 * 80 + 16}"
  then have "j \<in> set [1280..<1296]" unfolding set_upt by simp
  then have "j \<in> set [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]" unfolding upt_c30_080 .
  then show "oc_sub oc_b30 j" using oc_c30_1280 oc_c30_1281 oc_c30_1282 oc_c30_1283 oc_c30_1284 oc_c30_1285 oc_c30_1286 oc_c30_1287 oc_c30_1288 oc_c30_1289 oc_c30_1290 oc_c30_1291 oc_c30_1292 oc_c30_1293 oc_c30_1294 oc_c30_1295
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
