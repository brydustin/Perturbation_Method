theory GOCX_nc_092
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1472: "goc_sub None 1472"
  by (goc_eval goc_nc_1472)

lemma goc_nc_1473: "goc_sub None 1473"
  by (goc_eval goc_nc_1473)

lemma goc_nc_1474: "goc_sub None 1474"
  by (goc_eval goc_nc_1474)

lemma goc_nc_1475: "goc_sub None 1475"
  by (goc_eval goc_nc_1475)

lemma goc_nc_1476: "goc_sub None 1476"
  by (goc_eval goc_nc_1476)

lemma goc_nc_1477: "goc_sub None 1477"
  by (goc_eval goc_nc_1477)

lemma goc_nc_1478: "goc_sub None 1478"
  by (goc_eval goc_nc_1478)

lemma goc_nc_1479: "goc_sub None 1479"
  by (goc_eval goc_nc_1479)

lemma goc_nc_1480: "goc_sub None 1480"
  by (goc_eval goc_nc_1480)

lemma goc_nc_1481: "goc_sub None 1481"
  by (goc_eval goc_nc_1481)

lemma goc_nc_1482: "goc_sub None 1482"
  by (goc_eval goc_nc_1482)

lemma goc_nc_1483: "goc_sub None 1483"
  by (goc_eval goc_nc_1483)

lemma goc_nc_1484: "goc_sub None 1484"
  by (goc_eval goc_nc_1484)

lemma goc_nc_1485: "goc_sub None 1485"
  by (goc_eval goc_nc_1485)

lemma goc_nc_1486: "goc_sub None 1486"
  by (goc_eval goc_nc_1486)

lemma goc_nc_1487: "goc_sub None 1487"
  by (goc_eval goc_nc_1487)

lemma gupt_nc_092: "[1472..<1488] = [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]"
  by (simp add: upt_rec)

lemma gsec_nc_092: "\<forall>j\<in>{16 * 92..<16 * 92 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 92..<16 * 92 + 16}"
  then have "j \<in> set [1472..<1488]" unfolding set_upt by simp
  then have "j \<in> set [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]" unfolding gupt_nc_092 .
  then show "goc_sub None j" using goc_nc_1472 goc_nc_1473 goc_nc_1474 goc_nc_1475 goc_nc_1476 goc_nc_1477 goc_nc_1478 goc_nc_1479 goc_nc_1480 goc_nc_1481 goc_nc_1482 goc_nc_1483 goc_nc_1484 goc_nc_1485 goc_nc_1486 goc_nc_1487
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
