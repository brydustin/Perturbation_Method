theory OCX_c30_095
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1520: "oc_sub oc_b30 1520"
  by (oc_eval oc_c30_1520)

lemma oc_c30_1521: "oc_sub oc_b30 1521"
  by (oc_eval oc_c30_1521)

lemma oc_c30_1522: "oc_sub oc_b30 1522"
  by (oc_eval oc_c30_1522)

lemma oc_c30_1523: "oc_sub oc_b30 1523"
  by (oc_eval oc_c30_1523)

lemma oc_c30_1524: "oc_sub oc_b30 1524"
  by (oc_eval oc_c30_1524)

lemma oc_c30_1525: "oc_sub oc_b30 1525"
  by (oc_eval oc_c30_1525)

lemma oc_c30_1526: "oc_sub oc_b30 1526"
  by (oc_eval oc_c30_1526)

lemma oc_c30_1527: "oc_sub oc_b30 1527"
  by (oc_eval oc_c30_1527)

lemma oc_c30_1528: "oc_sub oc_b30 1528"
  by (oc_eval oc_c30_1528)

lemma oc_c30_1529: "oc_sub oc_b30 1529"
  by (oc_eval oc_c30_1529)

lemma oc_c30_1530: "oc_sub oc_b30 1530"
  by (oc_eval oc_c30_1530)

lemma oc_c30_1531: "oc_sub oc_b30 1531"
  by (oc_eval oc_c30_1531)

lemma oc_c30_1532: "oc_sub oc_b30 1532"
  by (oc_eval oc_c30_1532)

lemma oc_c30_1533: "oc_sub oc_b30 1533"
  by (oc_eval oc_c30_1533)

lemma oc_c30_1534: "oc_sub oc_b30 1534"
  by (oc_eval oc_c30_1534)

lemma oc_c30_1535: "oc_sub oc_b30 1535"
  by (oc_eval oc_c30_1535)

lemma upt_c30_095: "[1520..<1536] = [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]"
  by (simp add: upt_rec)

lemma sec_c30_095: "\<forall>j\<in>{16 * 95..<16 * 95 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 95..<16 * 95 + 16}"
  then have "j \<in> set [1520..<1536]" unfolding set_upt by simp
  then have "j \<in> set [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]" unfolding upt_c30_095 .
  then show "oc_sub oc_b30 j" using oc_c30_1520 oc_c30_1521 oc_c30_1522 oc_c30_1523 oc_c30_1524 oc_c30_1525 oc_c30_1526 oc_c30_1527 oc_c30_1528 oc_c30_1529 oc_c30_1530 oc_c30_1531 oc_c30_1532 oc_c30_1533 oc_c30_1534 oc_c30_1535
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
