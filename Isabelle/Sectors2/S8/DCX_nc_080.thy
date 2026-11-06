theory DCX_nc_080
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1280: "dc_sub None 1280"
  by (dc_eval dc_nc_1280)

lemma dc_nc_1281: "dc_sub None 1281"
  by (dc_eval dc_nc_1281)

lemma dc_nc_1282: "dc_sub None 1282"
  by (dc_eval dc_nc_1282)

lemma dc_nc_1283: "dc_sub None 1283"
  by (dc_eval dc_nc_1283)

lemma dc_nc_1284: "dc_sub None 1284"
  by (dc_eval dc_nc_1284)

lemma dc_nc_1285: "dc_sub None 1285"
  by (dc_eval dc_nc_1285)

lemma dc_nc_1286: "dc_sub None 1286"
  by (dc_eval dc_nc_1286)

lemma dc_nc_1287: "dc_sub None 1287"
  by (dc_eval dc_nc_1287)

lemma dc_nc_1288: "dc_sub None 1288"
  by (dc_eval dc_nc_1288)

lemma dc_nc_1289: "dc_sub None 1289"
  by (dc_eval dc_nc_1289)

lemma dc_nc_1290: "dc_sub None 1290"
  by (dc_eval dc_nc_1290)

lemma dc_nc_1291: "dc_sub None 1291"
  by (dc_eval dc_nc_1291)

lemma dc_nc_1292: "dc_sub None 1292"
  by (dc_eval dc_nc_1292)

lemma dc_nc_1293: "dc_sub None 1293"
  by (dc_eval dc_nc_1293)

lemma dc_nc_1294: "dc_sub None 1294"
  by (dc_eval dc_nc_1294)

lemma dc_nc_1295: "dc_sub None 1295"
  by (dc_eval dc_nc_1295)

lemma upt_nc_080: "[1280..<1296] = [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]"
  by (simp add: upt_rec)

lemma sec_nc_080: "\<forall>j\<in>{16 * 80..<16 * 80 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 80..<16 * 80 + 16}"
  then have "j \<in> set [1280..<1296]" unfolding set_upt by simp
  then have "j \<in> set [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]" unfolding upt_nc_080 .
  then show "dc_sub None j" using dc_nc_1280 dc_nc_1281 dc_nc_1282 dc_nc_1283 dc_nc_1284 dc_nc_1285 dc_nc_1286 dc_nc_1287 dc_nc_1288 dc_nc_1289 dc_nc_1290 dc_nc_1291 dc_nc_1292 dc_nc_1293 dc_nc_1294 dc_nc_1295
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
