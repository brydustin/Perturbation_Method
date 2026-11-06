theory DCX_nc_089
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1424: "dc_sub None 1424"
  by (dc_eval dc_nc_1424)

lemma dc_nc_1425: "dc_sub None 1425"
  by (dc_eval dc_nc_1425)

lemma dc_nc_1426: "dc_sub None 1426"
  by (dc_eval dc_nc_1426)

lemma dc_nc_1427: "dc_sub None 1427"
  by (dc_eval dc_nc_1427)

lemma dc_nc_1428: "dc_sub None 1428"
  by (dc_eval dc_nc_1428)

lemma dc_nc_1429: "dc_sub None 1429"
  by (dc_eval dc_nc_1429)

lemma dc_nc_1430: "dc_sub None 1430"
  by (dc_eval dc_nc_1430)

lemma dc_nc_1431: "dc_sub None 1431"
  by (dc_eval dc_nc_1431)

lemma dc_nc_1432: "dc_sub None 1432"
  by (dc_eval dc_nc_1432)

lemma dc_nc_1433: "dc_sub None 1433"
  by (dc_eval dc_nc_1433)

lemma dc_nc_1434: "dc_sub None 1434"
  by (dc_eval dc_nc_1434)

lemma dc_nc_1435: "dc_sub None 1435"
  by (dc_eval dc_nc_1435)

lemma dc_nc_1436: "dc_sub None 1436"
  by (dc_eval dc_nc_1436)

lemma dc_nc_1437: "dc_sub None 1437"
  by (dc_eval dc_nc_1437)

lemma dc_nc_1438: "dc_sub None 1438"
  by (dc_eval dc_nc_1438)

lemma dc_nc_1439: "dc_sub None 1439"
  by (dc_eval dc_nc_1439)

lemma upt_nc_089: "[1424..<1440] = [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]"
  by (simp add: upt_rec)

lemma sec_nc_089: "\<forall>j\<in>{16 * 89..<16 * 89 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 89..<16 * 89 + 16}"
  then have "j \<in> set [1424..<1440]" unfolding set_upt by simp
  then have "j \<in> set [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]" unfolding upt_nc_089 .
  then show "dc_sub None j" using dc_nc_1424 dc_nc_1425 dc_nc_1426 dc_nc_1427 dc_nc_1428 dc_nc_1429 dc_nc_1430 dc_nc_1431 dc_nc_1432 dc_nc_1433 dc_nc_1434 dc_nc_1435 dc_nc_1436 dc_nc_1437 dc_nc_1438 dc_nc_1439
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
