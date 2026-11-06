theory GDCX_nc_089
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1424: "gdc_sub None 1424"
  by (gdc_eval gdc_nc_1424)

lemma gdc_nc_1425: "gdc_sub None 1425"
  by (gdc_eval gdc_nc_1425)

lemma gdc_nc_1426: "gdc_sub None 1426"
  by (gdc_eval gdc_nc_1426)

lemma gdc_nc_1427: "gdc_sub None 1427"
  by (gdc_eval gdc_nc_1427)

lemma gdc_nc_1428: "gdc_sub None 1428"
  by (gdc_eval gdc_nc_1428)

lemma gdc_nc_1429: "gdc_sub None 1429"
  by (gdc_eval gdc_nc_1429)

lemma gdc_nc_1430: "gdc_sub None 1430"
  by (gdc_eval gdc_nc_1430)

lemma gdc_nc_1431: "gdc_sub None 1431"
  by (gdc_eval gdc_nc_1431)

lemma gdc_nc_1432: "gdc_sub None 1432"
  by (gdc_eval gdc_nc_1432)

lemma gdc_nc_1433: "gdc_sub None 1433"
  by (gdc_eval gdc_nc_1433)

lemma gdc_nc_1434: "gdc_sub None 1434"
  by (gdc_eval gdc_nc_1434)

lemma gdc_nc_1435: "gdc_sub None 1435"
  by (gdc_eval gdc_nc_1435)

lemma gdc_nc_1436: "gdc_sub None 1436"
  by (gdc_eval gdc_nc_1436)

lemma gdc_nc_1437: "gdc_sub None 1437"
  by (gdc_eval gdc_nc_1437)

lemma gdc_nc_1438: "gdc_sub None 1438"
  by (gdc_eval gdc_nc_1438)

lemma gdc_nc_1439: "gdc_sub None 1439"
  by (gdc_eval gdc_nc_1439)

lemma gupt_nc_089: "[1424..<1440] = [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]"
  by (simp add: upt_rec)

lemma gsec_nc_089: "\<forall>j\<in>{16 * 89..<16 * 89 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 89..<16 * 89 + 16}"
  then have "j \<in> set [1424..<1440]" unfolding set_upt by simp
  then have "j \<in> set [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]" unfolding gupt_nc_089 .
  then show "gdc_sub None j" using gdc_nc_1424 gdc_nc_1425 gdc_nc_1426 gdc_nc_1427 gdc_nc_1428 gdc_nc_1429 gdc_nc_1430 gdc_nc_1431 gdc_nc_1432 gdc_nc_1433 gdc_nc_1434 gdc_nc_1435 gdc_nc_1436 gdc_nc_1437 gdc_nc_1438 gdc_nc_1439
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
