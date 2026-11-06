theory GOCX_nc_089
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1424: "goc_sub None 1424"
  by (goc_eval goc_nc_1424)

lemma goc_nc_1425: "goc_sub None 1425"
  by (goc_eval goc_nc_1425)

lemma goc_nc_1426: "goc_sub None 1426"
  by (goc_eval goc_nc_1426)

lemma goc_nc_1427: "goc_sub None 1427"
  by (goc_eval goc_nc_1427)

lemma goc_nc_1428: "goc_sub None 1428"
  by (goc_eval goc_nc_1428)

lemma goc_nc_1429: "goc_sub None 1429"
  by (goc_eval goc_nc_1429)

lemma goc_nc_1430: "goc_sub None 1430"
  by (goc_eval goc_nc_1430)

lemma goc_nc_1431: "goc_sub None 1431"
  by (goc_eval goc_nc_1431)

lemma goc_nc_1432: "goc_sub None 1432"
  by (goc_eval goc_nc_1432)

lemma goc_nc_1433: "goc_sub None 1433"
  by (goc_eval goc_nc_1433)

lemma goc_nc_1434: "goc_sub None 1434"
  by (goc_eval goc_nc_1434)

lemma goc_nc_1435: "goc_sub None 1435"
  by (goc_eval goc_nc_1435)

lemma goc_nc_1436: "goc_sub None 1436"
  by (goc_eval goc_nc_1436)

lemma goc_nc_1437: "goc_sub None 1437"
  by (goc_eval goc_nc_1437)

lemma goc_nc_1438: "goc_sub None 1438"
  by (goc_eval goc_nc_1438)

lemma goc_nc_1439: "goc_sub None 1439"
  by (goc_eval goc_nc_1439)

lemma gupt_nc_089: "[1424..<1440] = [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]"
  by (simp add: upt_rec)

lemma gsec_nc_089: "\<forall>j\<in>{16 * 89..<16 * 89 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 89..<16 * 89 + 16}"
  then have "j \<in> set [1424..<1440]" unfolding set_upt by simp
  then have "j \<in> set [1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439]" unfolding gupt_nc_089 .
  then show "goc_sub None j" using goc_nc_1424 goc_nc_1425 goc_nc_1426 goc_nc_1427 goc_nc_1428 goc_nc_1429 goc_nc_1430 goc_nc_1431 goc_nc_1432 goc_nc_1433 goc_nc_1434 goc_nc_1435 goc_nc_1436 goc_nc_1437 goc_nc_1438 goc_nc_1439
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
