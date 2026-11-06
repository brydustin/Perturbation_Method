theory OCX_nc_080
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1280: "oc_sub None 1280"
  by (oc_eval oc_nc_1280)

lemma oc_nc_1281: "oc_sub None 1281"
  by (oc_eval oc_nc_1281)

lemma oc_nc_1282: "oc_sub None 1282"
  by (oc_eval oc_nc_1282)

lemma oc_nc_1283: "oc_sub None 1283"
  by (oc_eval oc_nc_1283)

lemma oc_nc_1284: "oc_sub None 1284"
  by (oc_eval oc_nc_1284)

lemma oc_nc_1285: "oc_sub None 1285"
  by (oc_eval oc_nc_1285)

lemma oc_nc_1286: "oc_sub None 1286"
  by (oc_eval oc_nc_1286)

lemma oc_nc_1287: "oc_sub None 1287"
  by (oc_eval oc_nc_1287)

lemma oc_nc_1288: "oc_sub None 1288"
  by (oc_eval oc_nc_1288)

lemma oc_nc_1289: "oc_sub None 1289"
  by (oc_eval oc_nc_1289)

lemma oc_nc_1290: "oc_sub None 1290"
  by (oc_eval oc_nc_1290)

lemma oc_nc_1291: "oc_sub None 1291"
  by (oc_eval oc_nc_1291)

lemma oc_nc_1292: "oc_sub None 1292"
  by (oc_eval oc_nc_1292)

lemma oc_nc_1293: "oc_sub None 1293"
  by (oc_eval oc_nc_1293)

lemma oc_nc_1294: "oc_sub None 1294"
  by (oc_eval oc_nc_1294)

lemma oc_nc_1295: "oc_sub None 1295"
  by (oc_eval oc_nc_1295)

lemma upt_nc_080: "[1280..<1296] = [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]"
  by (simp add: upt_rec)

lemma sec_nc_080: "\<forall>j\<in>{16 * 80..<16 * 80 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 80..<16 * 80 + 16}"
  then have "j \<in> set [1280..<1296]" unfolding set_upt by simp
  then have "j \<in> set [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]" unfolding upt_nc_080 .
  then show "oc_sub None j" using oc_nc_1280 oc_nc_1281 oc_nc_1282 oc_nc_1283 oc_nc_1284 oc_nc_1285 oc_nc_1286 oc_nc_1287 oc_nc_1288 oc_nc_1289 oc_nc_1290 oc_nc_1291 oc_nc_1292 oc_nc_1293 oc_nc_1294 oc_nc_1295
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
