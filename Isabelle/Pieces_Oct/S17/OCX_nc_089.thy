theory OCX_nc_089
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1424: "oc_sub None 1424"
  by (oc_eval oc_nc_1424)

lemma oc_nc_1425: "oc_sub None 1425"
  by (oc_eval oc_nc_1425)

lemma oc_nc_1426: "oc_sub None 1426"
  by (oc_eval oc_nc_1426)

lemma oc_nc_1427: "oc_sub None 1427"
  by (oc_eval oc_nc_1427)

lemma oc_nc_1428: "oc_sub None 1428"
  by (oc_eval oc_nc_1428)

lemma oc_nc_1429: "oc_sub None 1429"
  by (oc_eval oc_nc_1429)

lemma oc_nc_1430: "oc_sub None 1430"
  by (oc_eval oc_nc_1430)

lemma oc_nc_1431: "oc_sub None 1431"
  by (oc_eval oc_nc_1431)

lemma oc_nc_1432: "oc_sub None 1432"
  by (oc_eval oc_nc_1432)

lemma oc_nc_1433: "oc_sub None 1433"
  by (oc_eval oc_nc_1433)

lemma oc_nc_1434: "oc_sub None 1434"
  by (oc_eval oc_nc_1434)

lemma oc_nc_1435: "oc_sub None 1435"
  by (oc_eval oc_nc_1435)

lemma oc_nc_1436: "oc_sub None 1436"
  by (oc_eval oc_nc_1436)

lemma oc_nc_1437: "oc_sub None 1437"
  by (oc_eval oc_nc_1437)

lemma oc_nc_1438: "oc_sub None 1438"
  by (oc_eval oc_nc_1438)

lemma oc_nc_1439: "oc_sub None 1439"
  by (oc_eval oc_nc_1439)

lemma upt_nc_089: "[1424..<1440] = [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]"
  by (simp add: upt_rec)

lemma sec_nc_089: "\<forall>j\<in>{16 * 89..<16 * 89 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 89..<16 * 89 + 16}"
  then have "j \<in> set [1424..<1440]" unfolding set_upt by simp
  then have "j \<in> set [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]" unfolding upt_nc_089 .
  then show "oc_sub None j" using oc_nc_1424 oc_nc_1425 oc_nc_1426 oc_nc_1427 oc_nc_1428 oc_nc_1429 oc_nc_1430 oc_nc_1431 oc_nc_1432 oc_nc_1433 oc_nc_1434 oc_nc_1435 oc_nc_1436 oc_nc_1437 oc_nc_1438 oc_nc_1439
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
