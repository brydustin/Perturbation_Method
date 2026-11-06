theory OCX_nc_085
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1360: "oc_sub None 1360"
  by (oc_eval oc_nc_1360)

lemma oc_nc_1361: "oc_sub None 1361"
  by (oc_eval oc_nc_1361)

lemma oc_nc_1362: "oc_sub None 1362"
  by (oc_eval oc_nc_1362)

lemma oc_nc_1363: "oc_sub None 1363"
  by (oc_eval oc_nc_1363)

lemma oc_nc_1364: "oc_sub None 1364"
  by (oc_eval oc_nc_1364)

lemma oc_nc_1365: "oc_sub None 1365"
  by (oc_eval oc_nc_1365)

lemma oc_nc_1366: "oc_sub None 1366"
  by (oc_eval oc_nc_1366)

lemma oc_nc_1367: "oc_sub None 1367"
  by (oc_eval oc_nc_1367)

lemma oc_nc_1368: "oc_sub None 1368"
  by (oc_eval oc_nc_1368)

lemma oc_nc_1369: "oc_sub None 1369"
  by (oc_eval oc_nc_1369)

lemma oc_nc_1370: "oc_sub None 1370"
  by (oc_eval oc_nc_1370)

lemma oc_nc_1371: "oc_sub None 1371"
  by (oc_eval oc_nc_1371)

lemma oc_nc_1372: "oc_sub None 1372"
  by (oc_eval oc_nc_1372)

lemma oc_nc_1373: "oc_sub None 1373"
  by (oc_eval oc_nc_1373)

lemma oc_nc_1374: "oc_sub None 1374"
  by (oc_eval oc_nc_1374)

lemma oc_nc_1375: "oc_sub None 1375"
  by (oc_eval oc_nc_1375)

lemma upt_nc_085: "[1360..<1376] = [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]"
  by (simp add: upt_rec)

lemma sec_nc_085: "\<forall>j\<in>{16 * 85..<16 * 85 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 85..<16 * 85 + 16}"
  then have "j \<in> set [1360..<1376]" unfolding set_upt by simp
  then have "j \<in> set [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]" unfolding upt_nc_085 .
  then show "oc_sub None j" using oc_nc_1360 oc_nc_1361 oc_nc_1362 oc_nc_1363 oc_nc_1364 oc_nc_1365 oc_nc_1366 oc_nc_1367 oc_nc_1368 oc_nc_1369 oc_nc_1370 oc_nc_1371 oc_nc_1372 oc_nc_1373 oc_nc_1374 oc_nc_1375
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
