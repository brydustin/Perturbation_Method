theory DCX_c30_080
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1280: "dc_sub dc_b30 1280"
  by (dc_eval dc_c30_1280)

lemma dc_c30_1281: "dc_sub dc_b30 1281"
  by (dc_eval dc_c30_1281)

lemma dc_c30_1282: "dc_sub dc_b30 1282"
  by (dc_eval dc_c30_1282)

lemma dc_c30_1283: "dc_sub dc_b30 1283"
  by (dc_eval dc_c30_1283)

lemma dc_c30_1284: "dc_sub dc_b30 1284"
  by (dc_eval dc_c30_1284)

lemma dc_c30_1285: "dc_sub dc_b30 1285"
  by (dc_eval dc_c30_1285)

lemma dc_c30_1286: "dc_sub dc_b30 1286"
  by (dc_eval dc_c30_1286)

lemma dc_c30_1287: "dc_sub dc_b30 1287"
  by (dc_eval dc_c30_1287)

lemma dc_c30_1288: "dc_sub dc_b30 1288"
  by (dc_eval dc_c30_1288)

lemma dc_c30_1289: "dc_sub dc_b30 1289"
  by (dc_eval dc_c30_1289)

lemma dc_c30_1290: "dc_sub dc_b30 1290"
  by (dc_eval dc_c30_1290)

lemma dc_c30_1291: "dc_sub dc_b30 1291"
  by (dc_eval dc_c30_1291)

lemma dc_c30_1292: "dc_sub dc_b30 1292"
  by (dc_eval dc_c30_1292)

lemma dc_c30_1293: "dc_sub dc_b30 1293"
  by (dc_eval dc_c30_1293)

lemma dc_c30_1294: "dc_sub dc_b30 1294"
  by (dc_eval dc_c30_1294)

lemma dc_c30_1295: "dc_sub dc_b30 1295"
  by (dc_eval dc_c30_1295)

lemma upt_c30_080: "[1280..<1296] = [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]"
  by (simp add: upt_rec)

lemma sec_c30_080: "\<forall>j\<in>{16 * 80..<16 * 80 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 80..<16 * 80 + 16}"
  then have "j \<in> set [1280..<1296]" unfolding set_upt by simp
  then have "j \<in> set [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]" unfolding upt_c30_080 .
  then show "dc_sub dc_b30 j" using dc_c30_1280 dc_c30_1281 dc_c30_1282 dc_c30_1283 dc_c30_1284 dc_c30_1285 dc_c30_1286 dc_c30_1287 dc_c30_1288 dc_c30_1289 dc_c30_1290 dc_c30_1291 dc_c30_1292 dc_c30_1293 dc_c30_1294 dc_c30_1295
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
