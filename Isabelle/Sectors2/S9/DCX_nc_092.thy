theory DCX_nc_092
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1472: "dc_sub None 1472"
  by (dc_eval dc_nc_1472)

lemma dc_nc_1473: "dc_sub None 1473"
  by (dc_eval dc_nc_1473)

lemma dc_nc_1474: "dc_sub None 1474"
  by (dc_eval dc_nc_1474)

lemma dc_nc_1475: "dc_sub None 1475"
  by (dc_eval dc_nc_1475)

lemma dc_nc_1476: "dc_sub None 1476"
  by (dc_eval dc_nc_1476)

lemma dc_nc_1477: "dc_sub None 1477"
  by (dc_eval dc_nc_1477)

lemma dc_nc_1478: "dc_sub None 1478"
  by (dc_eval dc_nc_1478)

lemma dc_nc_1479: "dc_sub None 1479"
  by (dc_eval dc_nc_1479)

lemma dc_nc_1480: "dc_sub None 1480"
  by (dc_eval dc_nc_1480)

lemma dc_nc_1481: "dc_sub None 1481"
  by (dc_eval dc_nc_1481)

lemma dc_nc_1482: "dc_sub None 1482"
  by (dc_eval dc_nc_1482)

lemma dc_nc_1483: "dc_sub None 1483"
  by (dc_eval dc_nc_1483)

lemma dc_nc_1484: "dc_sub None 1484"
  by (dc_eval dc_nc_1484)

lemma dc_nc_1485: "dc_sub None 1485"
  by (dc_eval dc_nc_1485)

lemma dc_nc_1486: "dc_sub None 1486"
  by (dc_eval dc_nc_1486)

lemma dc_nc_1487: "dc_sub None 1487"
  by (dc_eval dc_nc_1487)

lemma upt_nc_092: "[1472..<1488] = [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]"
  by (simp add: upt_rec)

lemma sec_nc_092: "\<forall>j\<in>{16 * 92..<16 * 92 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 92..<16 * 92 + 16}"
  then have "j \<in> set [1472..<1488]" unfolding set_upt by simp
  then have "j \<in> set [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]" unfolding upt_nc_092 .
  then show "dc_sub None j" using dc_nc_1472 dc_nc_1473 dc_nc_1474 dc_nc_1475 dc_nc_1476 dc_nc_1477 dc_nc_1478 dc_nc_1479 dc_nc_1480 dc_nc_1481 dc_nc_1482 dc_nc_1483 dc_nc_1484 dc_nc_1485 dc_nc_1486 dc_nc_1487
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
