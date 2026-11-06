theory DCX_c30_095
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1520: "dc_sub dc_b30 1520"
  by (dc_eval dc_c30_1520)

lemma dc_c30_1521: "dc_sub dc_b30 1521"
  by (dc_eval dc_c30_1521)

lemma dc_c30_1522: "dc_sub dc_b30 1522"
  by (dc_eval dc_c30_1522)

lemma dc_c30_1523: "dc_sub dc_b30 1523"
  by (dc_eval dc_c30_1523)

lemma dc_c30_1524: "dc_sub dc_b30 1524"
  by (dc_eval dc_c30_1524)

lemma dc_c30_1525: "dc_sub dc_b30 1525"
  by (dc_eval dc_c30_1525)

lemma dc_c30_1526: "dc_sub dc_b30 1526"
  by (dc_eval dc_c30_1526)

lemma dc_c30_1527: "dc_sub dc_b30 1527"
  by (dc_eval dc_c30_1527)

lemma dc_c30_1528: "dc_sub dc_b30 1528"
  by (dc_eval dc_c30_1528)

lemma dc_c30_1529: "dc_sub dc_b30 1529"
  by (dc_eval dc_c30_1529)

lemma dc_c30_1530: "dc_sub dc_b30 1530"
  by (dc_eval dc_c30_1530)

lemma dc_c30_1531: "dc_sub dc_b30 1531"
  by (dc_eval dc_c30_1531)

lemma dc_c30_1532: "dc_sub dc_b30 1532"
  by (dc_eval dc_c30_1532)

lemma dc_c30_1533: "dc_sub dc_b30 1533"
  by (dc_eval dc_c30_1533)

lemma dc_c30_1534: "dc_sub dc_b30 1534"
  by (dc_eval dc_c30_1534)

lemma dc_c30_1535: "dc_sub dc_b30 1535"
  by (dc_eval dc_c30_1535)

lemma upt_c30_095: "[1520..<1536] = [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]"
  by (simp add: upt_rec)

lemma sec_c30_095: "\<forall>j\<in>{16 * 95..<16 * 95 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 95..<16 * 95 + 16}"
  then have "j \<in> set [1520..<1536]" unfolding set_upt by simp
  then have "j \<in> set [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]" unfolding upt_c30_095 .
  then show "dc_sub dc_b30 j" using dc_c30_1520 dc_c30_1521 dc_c30_1522 dc_c30_1523 dc_c30_1524 dc_c30_1525 dc_c30_1526 dc_c30_1527 dc_c30_1528 dc_c30_1529 dc_c30_1530 dc_c30_1531 dc_c30_1532 dc_c30_1533 dc_c30_1534 dc_c30_1535
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
