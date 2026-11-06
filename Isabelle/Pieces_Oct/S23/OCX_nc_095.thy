theory OCX_nc_095
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1520: "oc_sub None 1520"
  by (oc_eval oc_nc_1520)

lemma oc_nc_1521: "oc_sub None 1521"
  by (oc_eval oc_nc_1521)

lemma oc_nc_1522: "oc_sub None 1522"
  by (oc_eval oc_nc_1522)

lemma oc_nc_1523: "oc_sub None 1523"
  by (oc_eval oc_nc_1523)

lemma oc_nc_1524: "oc_sub None 1524"
  by (oc_eval oc_nc_1524)

lemma oc_nc_1525: "oc_sub None 1525"
  by (oc_eval oc_nc_1525)

lemma oc_nc_1526: "oc_sub None 1526"
  by (oc_eval oc_nc_1526)

lemma oc_nc_1527: "oc_sub None 1527"
  by (oc_eval oc_nc_1527)

lemma oc_nc_1528: "oc_sub None 1528"
  by (oc_eval oc_nc_1528)

lemma oc_nc_1529: "oc_sub None 1529"
  by (oc_eval oc_nc_1529)

lemma oc_nc_1530: "oc_sub None 1530"
  by (oc_eval oc_nc_1530)

lemma oc_nc_1531: "oc_sub None 1531"
  by (oc_eval oc_nc_1531)

lemma oc_nc_1532: "oc_sub None 1532"
  by (oc_eval oc_nc_1532)

lemma oc_nc_1533: "oc_sub None 1533"
  by (oc_eval oc_nc_1533)

lemma oc_nc_1534: "oc_sub None 1534"
  by (oc_eval oc_nc_1534)

lemma oc_nc_1535: "oc_sub None 1535"
  by (oc_eval oc_nc_1535)

lemma upt_nc_095: "[1520..<1536] = [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]"
  by (simp add: upt_rec)

lemma sec_nc_095: "\<forall>j\<in>{16 * 95..<16 * 95 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 95..<16 * 95 + 16}"
  then have "j \<in> set [1520..<1536]" unfolding set_upt by simp
  then have "j \<in> set [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]" unfolding upt_nc_095 .
  then show "oc_sub None j" using oc_nc_1520 oc_nc_1521 oc_nc_1522 oc_nc_1523 oc_nc_1524 oc_nc_1525 oc_nc_1526 oc_nc_1527 oc_nc_1528 oc_nc_1529 oc_nc_1530 oc_nc_1531 oc_nc_1532 oc_nc_1533 oc_nc_1534 oc_nc_1535
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
