theory OCX_c30_092
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1472: "oc_sub oc_b30 1472"
  by (oc_eval oc_c30_1472)

lemma oc_c30_1473: "oc_sub oc_b30 1473"
  by (oc_eval oc_c30_1473)

lemma oc_c30_1474: "oc_sub oc_b30 1474"
  by (oc_eval oc_c30_1474)

lemma oc_c30_1475: "oc_sub oc_b30 1475"
  by (oc_eval oc_c30_1475)

lemma oc_c30_1476: "oc_sub oc_b30 1476"
  by (oc_eval oc_c30_1476)

lemma oc_c30_1477: "oc_sub oc_b30 1477"
  by (oc_eval oc_c30_1477)

lemma oc_c30_1478: "oc_sub oc_b30 1478"
  by (oc_eval oc_c30_1478)

lemma oc_c30_1479: "oc_sub oc_b30 1479"
  by (oc_eval oc_c30_1479)

lemma oc_c30_1480: "oc_sub oc_b30 1480"
  by (oc_eval oc_c30_1480)

lemma oc_c30_1481: "oc_sub oc_b30 1481"
  by (oc_eval oc_c30_1481)

lemma oc_c30_1482: "oc_sub oc_b30 1482"
  by (oc_eval oc_c30_1482)

lemma oc_c30_1483: "oc_sub oc_b30 1483"
  by (oc_eval oc_c30_1483)

lemma oc_c30_1484: "oc_sub oc_b30 1484"
  by (oc_eval oc_c30_1484)

lemma oc_c30_1485: "oc_sub oc_b30 1485"
  by (oc_eval oc_c30_1485)

lemma oc_c30_1486: "oc_sub oc_b30 1486"
  by (oc_eval oc_c30_1486)

lemma oc_c30_1487: "oc_sub oc_b30 1487"
  by (oc_eval oc_c30_1487)

lemma upt_c30_092: "[1472..<1488] = [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]"
  by (simp add: upt_rec)

lemma sec_c30_092: "\<forall>j\<in>{16 * 92..<16 * 92 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 92..<16 * 92 + 16}"
  then have "j \<in> set [1472..<1488]" unfolding set_upt by simp
  then have "j \<in> set [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]" unfolding upt_c30_092 .
  then show "oc_sub oc_b30 j" using oc_c30_1472 oc_c30_1473 oc_c30_1474 oc_c30_1475 oc_c30_1476 oc_c30_1477 oc_c30_1478 oc_c30_1479 oc_c30_1480 oc_c30_1481 oc_c30_1482 oc_c30_1483 oc_c30_1484 oc_c30_1485 oc_c30_1486 oc_c30_1487
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
