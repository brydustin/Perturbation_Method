theory GOCX_nc_080
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1280: "goc_sub None 1280"
  by (goc_eval goc_nc_1280)

lemma goc_nc_1281: "goc_sub None 1281"
  by (goc_eval goc_nc_1281)

lemma goc_nc_1282: "goc_sub None 1282"
  by (goc_eval goc_nc_1282)

lemma goc_nc_1283: "goc_sub None 1283"
  by (goc_eval goc_nc_1283)

lemma goc_nc_1284: "goc_sub None 1284"
  by (goc_eval goc_nc_1284)

lemma goc_nc_1285: "goc_sub None 1285"
  by (goc_eval goc_nc_1285)

lemma goc_nc_1286: "goc_sub None 1286"
  by (goc_eval goc_nc_1286)

lemma goc_nc_1287: "goc_sub None 1287"
  by (goc_eval goc_nc_1287)

lemma goc_nc_1288: "goc_sub None 1288"
  by (goc_eval goc_nc_1288)

lemma goc_nc_1289: "goc_sub None 1289"
  by (goc_eval goc_nc_1289)

lemma goc_nc_1290: "goc_sub None 1290"
  by (goc_eval goc_nc_1290)

lemma goc_nc_1291: "goc_sub None 1291"
  by (goc_eval goc_nc_1291)

lemma goc_nc_1292: "goc_sub None 1292"
  by (goc_eval goc_nc_1292)

lemma goc_nc_1293: "goc_sub None 1293"
  by (goc_eval goc_nc_1293)

lemma goc_nc_1294: "goc_sub None 1294"
  by (goc_eval goc_nc_1294)

lemma goc_nc_1295: "goc_sub None 1295"
  by (goc_eval goc_nc_1295)

lemma gupt_nc_080: "[1280..<1296] = [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]"
  by (simp add: upt_rec)

lemma gsec_nc_080: "\<forall>j\<in>{16 * 80..<16 * 80 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 80..<16 * 80 + 16}"
  then have "j \<in> set [1280..<1296]" unfolding set_upt by simp
  then have "j \<in> set [1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295]" unfolding gupt_nc_080 .
  then show "goc_sub None j" using goc_nc_1280 goc_nc_1281 goc_nc_1282 goc_nc_1283 goc_nc_1284 goc_nc_1285 goc_nc_1286 goc_nc_1287 goc_nc_1288 goc_nc_1289 goc_nc_1290 goc_nc_1291 goc_nc_1292 goc_nc_1293 goc_nc_1294 goc_nc_1295
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
