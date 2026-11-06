theory GDCX_nc_080
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1280: "gdc_sub None 1280"
  by (gdc_eval gdc_nc_1280)

lemma gdc_nc_1281: "gdc_sub None 1281"
  by (gdc_eval gdc_nc_1281)

lemma gdc_nc_1282: "gdc_sub None 1282"
  by (gdc_eval gdc_nc_1282)

lemma gdc_nc_1283: "gdc_sub None 1283"
  by (gdc_eval gdc_nc_1283)

lemma gdc_nc_1284: "gdc_sub None 1284"
  by (gdc_eval gdc_nc_1284)

lemma gdc_nc_1285: "gdc_sub None 1285"
  by (gdc_eval gdc_nc_1285)

lemma gdc_nc_1286: "gdc_sub None 1286"
  by (gdc_eval gdc_nc_1286)

lemma gdc_nc_1287: "gdc_sub None 1287"
  by (gdc_eval gdc_nc_1287)

lemma gdc_nc_1288: "gdc_sub None 1288"
  by (gdc_eval gdc_nc_1288)

lemma gdc_nc_1289: "gdc_sub None 1289"
  by (gdc_eval gdc_nc_1289)

lemma gdc_nc_1290: "gdc_sub None 1290"
  by (gdc_eval gdc_nc_1290)

lemma gdc_nc_1291: "gdc_sub None 1291"
  by (gdc_eval gdc_nc_1291)

lemma gdc_nc_1292: "gdc_sub None 1292"
  by (gdc_eval gdc_nc_1292)

lemma gdc_nc_1293: "gdc_sub None 1293"
  by (gdc_eval gdc_nc_1293)

lemma gdc_nc_1294: "gdc_sub None 1294"
  by (gdc_eval gdc_nc_1294)

lemma gdc_nc_1295: "gdc_sub None 1295"
  by (gdc_eval gdc_nc_1295)

lemma gupt_nc_080: "[1280..<1296] = [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]"
  by (simp add: upt_rec)

lemma gsec_nc_080: "\<forall>j\<in>{16 * 80..<16 * 80 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 80..<16 * 80 + 16}"
  then have "j \<in> set [1280..<1296]" unfolding set_upt by simp
  then have "j \<in> set [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]" unfolding gupt_nc_080 .
  then show "gdc_sub None j" using gdc_nc_1280 gdc_nc_1281 gdc_nc_1282 gdc_nc_1283 gdc_nc_1284 gdc_nc_1285 gdc_nc_1286 gdc_nc_1287 gdc_nc_1288 gdc_nc_1289 gdc_nc_1290 gdc_nc_1291 gdc_nc_1292 gdc_nc_1293 gdc_nc_1294 gdc_nc_1295
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
