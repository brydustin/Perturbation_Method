theory OCX_c30_089
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1424: "oc_sub oc_b30 1424"
  by (oc_eval oc_c30_1424)

lemma oc_c30_1425: "oc_sub oc_b30 1425"
  by (oc_eval oc_c30_1425)

lemma oc_c30_1426: "oc_sub oc_b30 1426"
  by (oc_eval oc_c30_1426)

lemma oc_c30_1427: "oc_sub oc_b30 1427"
  by (oc_eval oc_c30_1427)

lemma oc_c30_1428: "oc_sub oc_b30 1428"
  by (oc_eval oc_c30_1428)

lemma oc_c30_1429: "oc_sub oc_b30 1429"
  by (oc_eval oc_c30_1429)

lemma oc_c30_1430: "oc_sub oc_b30 1430"
  by (oc_eval oc_c30_1430)

lemma oc_c30_1431: "oc_sub oc_b30 1431"
  by (oc_eval oc_c30_1431)

lemma oc_c30_1432: "oc_sub oc_b30 1432"
  by (oc_eval oc_c30_1432)

lemma oc_c30_1433: "oc_sub oc_b30 1433"
  by (oc_eval oc_c30_1433)

lemma oc_c30_1434: "oc_sub oc_b30 1434"
  by (oc_eval oc_c30_1434)

lemma oc_c30_1435: "oc_sub oc_b30 1435"
  by (oc_eval oc_c30_1435)

lemma oc_c30_1436: "oc_sub oc_b30 1436"
  by (oc_eval oc_c30_1436)

lemma oc_c30_1437: "oc_sub oc_b30 1437"
  by (oc_eval oc_c30_1437)

lemma oc_c30_1438: "oc_sub oc_b30 1438"
  by (oc_eval oc_c30_1438)

lemma oc_c30_1439: "oc_sub oc_b30 1439"
  by (oc_eval oc_c30_1439)

lemma upt_c30_089: "[1424..<1440] = [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]"
  by (simp add: upt_rec)

lemma sec_c30_089: "\<forall>j\<in>{16 * 89..<16 * 89 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 89..<16 * 89 + 16}"
  then have "j \<in> set [1424..<1440]" unfolding set_upt by simp
  then have "j \<in> set [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]" unfolding upt_c30_089 .
  then show "oc_sub oc_b30 j" using oc_c30_1424 oc_c30_1425 oc_c30_1426 oc_c30_1427 oc_c30_1428 oc_c30_1429 oc_c30_1430 oc_c30_1431 oc_c30_1432 oc_c30_1433 oc_c30_1434 oc_c30_1435 oc_c30_1436 oc_c30_1437 oc_c30_1438 oc_c30_1439
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
