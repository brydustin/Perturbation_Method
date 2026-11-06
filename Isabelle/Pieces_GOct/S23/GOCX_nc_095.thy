theory GOCX_nc_095
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1520: "goc_sub None 1520"
  by (goc_eval goc_nc_1520)

lemma goc_nc_1521: "goc_sub None 1521"
  by (goc_eval goc_nc_1521)

lemma goc_nc_1522: "goc_sub None 1522"
  by (goc_eval goc_nc_1522)

lemma goc_nc_1523: "goc_sub None 1523"
  by (goc_eval goc_nc_1523)

lemma goc_nc_1524: "goc_sub None 1524"
  by (goc_eval goc_nc_1524)

lemma goc_nc_1525: "goc_sub None 1525"
  by (goc_eval goc_nc_1525)

lemma goc_nc_1526: "goc_sub None 1526"
  by (goc_eval goc_nc_1526)

lemma goc_nc_1527: "goc_sub None 1527"
  by (goc_eval goc_nc_1527)

lemma goc_nc_1528: "goc_sub None 1528"
  by (goc_eval goc_nc_1528)

lemma goc_nc_1529: "goc_sub None 1529"
  by (goc_eval goc_nc_1529)

lemma goc_nc_1530: "goc_sub None 1530"
  by (goc_eval goc_nc_1530)

lemma goc_nc_1531: "goc_sub None 1531"
  by (goc_eval goc_nc_1531)

lemma goc_nc_1532: "goc_sub None 1532"
  by (goc_eval goc_nc_1532)

lemma goc_nc_1533: "goc_sub None 1533"
  by (goc_eval goc_nc_1533)

lemma goc_nc_1534: "goc_sub None 1534"
  by (goc_eval goc_nc_1534)

lemma goc_nc_1535: "goc_sub None 1535"
  by (goc_eval goc_nc_1535)

lemma gupt_nc_095: "[1520..<1536] = [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]"
  by (simp add: upt_rec)

lemma gsec_nc_095: "\<forall>j\<in>{16 * 95..<16 * 95 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 95..<16 * 95 + 16}"
  then have "j \<in> set [1520..<1536]" unfolding set_upt by simp
  then have "j \<in> set [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]" unfolding gupt_nc_095 .
  then show "goc_sub None j" using goc_nc_1520 goc_nc_1521 goc_nc_1522 goc_nc_1523 goc_nc_1524 goc_nc_1525 goc_nc_1526 goc_nc_1527 goc_nc_1528 goc_nc_1529 goc_nc_1530 goc_nc_1531 goc_nc_1532 goc_nc_1533 goc_nc_1534 goc_nc_1535
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
