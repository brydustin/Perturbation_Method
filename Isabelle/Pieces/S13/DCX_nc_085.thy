theory DCX_nc_085
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1360: "dc_sub None 1360"
  by (dc_eval dc_nc_1360)

lemma dc_nc_1361: "dc_sub None 1361"
  by (dc_eval dc_nc_1361)

lemma dc_nc_1362: "dc_sub None 1362"
  by (dc_eval dc_nc_1362)

lemma dc_nc_1363: "dc_sub None 1363"
  by (dc_eval dc_nc_1363)

lemma dc_nc_1364: "dc_sub None 1364"
  by (dc_eval dc_nc_1364)

lemma dc_nc_1365: "dc_sub None 1365"
  by (dc_eval dc_nc_1365)

lemma dc_nc_1366: "dc_sub None 1366"
  by (dc_eval dc_nc_1366)

lemma dc_nc_1367: "dc_sub None 1367"
  by (dc_eval dc_nc_1367)

lemma dc_nc_1368: "dc_sub None 1368"
  by (dc_eval dc_nc_1368)

lemma dc_nc_1369: "dc_sub None 1369"
  by (dc_eval dc_nc_1369)

lemma dc_nc_1370: "dc_sub None 1370"
  by (dc_eval dc_nc_1370)

lemma dc_nc_1371: "dc_sub None 1371"
  by (dc_eval dc_nc_1371)

lemma dc_nc_1372: "dc_sub None 1372"
  by (dc_eval dc_nc_1372)

lemma dc_nc_1373: "dc_sub None 1373"
  by (dc_eval dc_nc_1373)

lemma dc_nc_1374: "dc_sub None 1374"
  by (dc_eval dc_nc_1374)

lemma dc_nc_1375: "dc_sub None 1375"
  by (dc_eval dc_nc_1375)

lemma upt_nc_085: "[1360..<1376] = [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]"
  by (simp add: upt_rec)

lemma sec_nc_085: "\<forall>j\<in>{16 * 85..<16 * 85 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 85..<16 * 85 + 16}"
  then have "j \<in> set [1360..<1376]" unfolding set_upt by simp
  then have "j \<in> set [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]" unfolding upt_nc_085 .
  then show "dc_sub None j" using dc_nc_1360 dc_nc_1361 dc_nc_1362 dc_nc_1363 dc_nc_1364 dc_nc_1365 dc_nc_1366 dc_nc_1367 dc_nc_1368 dc_nc_1369 dc_nc_1370 dc_nc_1371 dc_nc_1372 dc_nc_1373 dc_nc_1374 dc_nc_1375
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
