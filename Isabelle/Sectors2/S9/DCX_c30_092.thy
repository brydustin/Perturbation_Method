theory DCX_c30_092
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1472: "dc_sub dc_b30 1472"
  by (dc_eval dc_c30_1472)

lemma dc_c30_1473: "dc_sub dc_b30 1473"
  by (dc_eval dc_c30_1473)

lemma dc_c30_1474: "dc_sub dc_b30 1474"
  by (dc_eval dc_c30_1474)

lemma dc_c30_1475: "dc_sub dc_b30 1475"
  by (dc_eval dc_c30_1475)

lemma dc_c30_1476: "dc_sub dc_b30 1476"
  by (dc_eval dc_c30_1476)

lemma dc_c30_1477: "dc_sub dc_b30 1477"
  by (dc_eval dc_c30_1477)

lemma dc_c30_1478: "dc_sub dc_b30 1478"
  by (dc_eval dc_c30_1478)

lemma dc_c30_1479: "dc_sub dc_b30 1479"
  by (dc_eval dc_c30_1479)

lemma dc_c30_1480: "dc_sub dc_b30 1480"
  by (dc_eval dc_c30_1480)

lemma dc_c30_1481: "dc_sub dc_b30 1481"
  by (dc_eval dc_c30_1481)

lemma dc_c30_1482: "dc_sub dc_b30 1482"
  by (dc_eval dc_c30_1482)

lemma dc_c30_1483: "dc_sub dc_b30 1483"
  by (dc_eval dc_c30_1483)

lemma dc_c30_1484: "dc_sub dc_b30 1484"
  by (dc_eval dc_c30_1484)

lemma dc_c30_1485: "dc_sub dc_b30 1485"
  by (dc_eval dc_c30_1485)

lemma dc_c30_1486: "dc_sub dc_b30 1486"
  by (dc_eval dc_c30_1486)

lemma dc_c30_1487: "dc_sub dc_b30 1487"
  by (dc_eval dc_c30_1487)

lemma upt_c30_092: "[1472..<1488] = [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]"
  by (simp add: upt_rec)

lemma sec_c30_092: "\<forall>j\<in>{16 * 92..<16 * 92 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 92..<16 * 92 + 16}"
  then have "j \<in> set [1472..<1488]" unfolding set_upt by simp
  then have "j \<in> set [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]" unfolding upt_c30_092 .
  then show "dc_sub dc_b30 j" using dc_c30_1472 dc_c30_1473 dc_c30_1474 dc_c30_1475 dc_c30_1476 dc_c30_1477 dc_c30_1478 dc_c30_1479 dc_c30_1480 dc_c30_1481 dc_c30_1482 dc_c30_1483 dc_c30_1484 dc_c30_1485 dc_c30_1486 dc_c30_1487
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
