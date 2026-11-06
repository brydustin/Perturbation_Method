theory GDCX_nc_085
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1360: "gdc_sub None 1360"
  by (gdc_eval gdc_nc_1360)

lemma gdc_nc_1361: "gdc_sub None 1361"
  by (gdc_eval gdc_nc_1361)

lemma gdc_nc_1362: "gdc_sub None 1362"
  by (gdc_eval gdc_nc_1362)

lemma gdc_nc_1363: "gdc_sub None 1363"
  by (gdc_eval gdc_nc_1363)

lemma gdc_nc_1364: "gdc_sub None 1364"
  by (gdc_eval gdc_nc_1364)

lemma gdc_nc_1365: "gdc_sub None 1365"
  by (gdc_eval gdc_nc_1365)

lemma gdc_nc_1366: "gdc_sub None 1366"
  by (gdc_eval gdc_nc_1366)

lemma gdc_nc_1367: "gdc_sub None 1367"
  by (gdc_eval gdc_nc_1367)

lemma gdc_nc_1368: "gdc_sub None 1368"
  by (gdc_eval gdc_nc_1368)

lemma gdc_nc_1369: "gdc_sub None 1369"
  by (gdc_eval gdc_nc_1369)

lemma gdc_nc_1370: "gdc_sub None 1370"
  by (gdc_eval gdc_nc_1370)

lemma gdc_nc_1371: "gdc_sub None 1371"
  by (gdc_eval gdc_nc_1371)

lemma gdc_nc_1372: "gdc_sub None 1372"
  by (gdc_eval gdc_nc_1372)

lemma gdc_nc_1373: "gdc_sub None 1373"
  by (gdc_eval gdc_nc_1373)

lemma gdc_nc_1374: "gdc_sub None 1374"
  by (gdc_eval gdc_nc_1374)

lemma gdc_nc_1375: "gdc_sub None 1375"
  by (gdc_eval gdc_nc_1375)

lemma gupt_nc_085: "[1360..<1376] = [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]"
  by (simp add: upt_rec)

lemma gsec_nc_085: "\<forall>j\<in>{16 * 85..<16 * 85 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 85..<16 * 85 + 16}"
  then have "j \<in> set [1360..<1376]" unfolding set_upt by simp
  then have "j \<in> set [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]" unfolding gupt_nc_085 .
  then show "gdc_sub None j" using gdc_nc_1360 gdc_nc_1361 gdc_nc_1362 gdc_nc_1363 gdc_nc_1364 gdc_nc_1365 gdc_nc_1366 gdc_nc_1367 gdc_nc_1368 gdc_nc_1369 gdc_nc_1370 gdc_nc_1371 gdc_nc_1372 gdc_nc_1373 gdc_nc_1374 gdc_nc_1375
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
