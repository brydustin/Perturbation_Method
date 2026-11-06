theory DCX_nc_095
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1520: "dc_sub None 1520"
  by (dc_eval dc_nc_1520)

lemma dc_nc_1521: "dc_sub None 1521"
  by (dc_eval dc_nc_1521)

lemma dc_nc_1522: "dc_sub None 1522"
  by (dc_eval dc_nc_1522)

lemma dc_nc_1523: "dc_sub None 1523"
  by (dc_eval dc_nc_1523)

lemma dc_nc_1524: "dc_sub None 1524"
  by (dc_eval dc_nc_1524)

lemma dc_nc_1525: "dc_sub None 1525"
  by (dc_eval dc_nc_1525)

lemma dc_nc_1526: "dc_sub None 1526"
  by (dc_eval dc_nc_1526)

lemma dc_nc_1527: "dc_sub None 1527"
  by (dc_eval dc_nc_1527)

lemma dc_nc_1528: "dc_sub None 1528"
  by (dc_eval dc_nc_1528)

lemma dc_nc_1529: "dc_sub None 1529"
  by (dc_eval dc_nc_1529)

lemma dc_nc_1530: "dc_sub None 1530"
  by (dc_eval dc_nc_1530)

lemma dc_nc_1531: "dc_sub None 1531"
  by (dc_eval dc_nc_1531)

lemma dc_nc_1532: "dc_sub None 1532"
  by (dc_eval dc_nc_1532)

lemma dc_nc_1533: "dc_sub None 1533"
  by (dc_eval dc_nc_1533)

lemma dc_nc_1534: "dc_sub None 1534"
  by (dc_eval dc_nc_1534)

lemma dc_nc_1535: "dc_sub None 1535"
  by (dc_eval dc_nc_1535)

lemma upt_nc_095: "[1520..<1536] = [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]"
  by (simp add: upt_rec)

lemma sec_nc_095: "\<forall>j\<in>{16 * 95..<16 * 95 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 95..<16 * 95 + 16}"
  then have "j \<in> set [1520..<1536]" unfolding set_upt by simp
  then have "j \<in> set [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]" unfolding upt_nc_095 .
  then show "dc_sub None j" using dc_nc_1520 dc_nc_1521 dc_nc_1522 dc_nc_1523 dc_nc_1524 dc_nc_1525 dc_nc_1526 dc_nc_1527 dc_nc_1528 dc_nc_1529 dc_nc_1530 dc_nc_1531 dc_nc_1532 dc_nc_1533 dc_nc_1534 dc_nc_1535
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
