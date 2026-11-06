theory GOCX_nc_085
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1360: "goc_sub None 1360"
  by (goc_eval goc_nc_1360)

lemma goc_nc_1361: "goc_sub None 1361"
  by (goc_eval goc_nc_1361)

lemma goc_nc_1362: "goc_sub None 1362"
  by (goc_eval goc_nc_1362)

lemma goc_nc_1363: "goc_sub None 1363"
  by (goc_eval goc_nc_1363)

lemma goc_nc_1364: "goc_sub None 1364"
  by (goc_eval goc_nc_1364)

lemma goc_nc_1365: "goc_sub None 1365"
  by (goc_eval goc_nc_1365)

lemma goc_nc_1366: "goc_sub None 1366"
  by (goc_eval goc_nc_1366)

lemma goc_nc_1367: "goc_sub None 1367"
  by (goc_eval goc_nc_1367)

lemma goc_nc_1368: "goc_sub None 1368"
  by (goc_eval goc_nc_1368)

lemma goc_nc_1369: "goc_sub None 1369"
  by (goc_eval goc_nc_1369)

lemma goc_nc_1370: "goc_sub None 1370"
  by (goc_eval goc_nc_1370)

lemma goc_nc_1371: "goc_sub None 1371"
  by (goc_eval goc_nc_1371)

lemma goc_nc_1372: "goc_sub None 1372"
  by (goc_eval goc_nc_1372)

lemma goc_nc_1373: "goc_sub None 1373"
  by (goc_eval goc_nc_1373)

lemma goc_nc_1374: "goc_sub None 1374"
  by (goc_eval goc_nc_1374)

lemma goc_nc_1375: "goc_sub None 1375"
  by (goc_eval goc_nc_1375)

lemma gupt_nc_085: "[1360..<1376] = [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]"
  by (simp add: upt_rec)

lemma gsec_nc_085: "\<forall>j\<in>{16 * 85..<16 * 85 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 85..<16 * 85 + 16}"
  then have "j \<in> set [1360..<1376]" unfolding set_upt by simp
  then have "j \<in> set [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]" unfolding gupt_nc_085 .
  then show "goc_sub None j" using goc_nc_1360 goc_nc_1361 goc_nc_1362 goc_nc_1363 goc_nc_1364 goc_nc_1365 goc_nc_1366 goc_nc_1367 goc_nc_1368 goc_nc_1369 goc_nc_1370 goc_nc_1371 goc_nc_1372 goc_nc_1373 goc_nc_1374 goc_nc_1375
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
