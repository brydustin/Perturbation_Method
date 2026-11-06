theory GDCX_nc_095
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1520: "gdc_sub None 1520"
  by (gdc_eval gdc_nc_1520)

lemma gdc_nc_1521: "gdc_sub None 1521"
  by (gdc_eval gdc_nc_1521)

lemma gdc_nc_1522: "gdc_sub None 1522"
  by (gdc_eval gdc_nc_1522)

lemma gdc_nc_1523: "gdc_sub None 1523"
  by (gdc_eval gdc_nc_1523)

lemma gdc_nc_1524: "gdc_sub None 1524"
  by (gdc_eval gdc_nc_1524)

lemma gdc_nc_1525: "gdc_sub None 1525"
  by (gdc_eval gdc_nc_1525)

lemma gdc_nc_1526: "gdc_sub None 1526"
  by (gdc_eval gdc_nc_1526)

lemma gdc_nc_1527: "gdc_sub None 1527"
  by (gdc_eval gdc_nc_1527)

lemma gdc_nc_1528: "gdc_sub None 1528"
  by (gdc_eval gdc_nc_1528)

lemma gdc_nc_1529: "gdc_sub None 1529"
  by (gdc_eval gdc_nc_1529)

lemma gdc_nc_1530: "gdc_sub None 1530"
  by (gdc_eval gdc_nc_1530)

lemma gdc_nc_1531: "gdc_sub None 1531"
  by (gdc_eval gdc_nc_1531)

lemma gdc_nc_1532: "gdc_sub None 1532"
  by (gdc_eval gdc_nc_1532)

lemma gdc_nc_1533: "gdc_sub None 1533"
  by (gdc_eval gdc_nc_1533)

lemma gdc_nc_1534: "gdc_sub None 1534"
  by (gdc_eval gdc_nc_1534)

lemma gdc_nc_1535: "gdc_sub None 1535"
  by (gdc_eval gdc_nc_1535)

lemma gupt_nc_095: "[1520..<1536] = [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]"
  by (simp add: upt_rec)

lemma gsec_nc_095: "\<forall>j\<in>{16 * 95..<16 * 95 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 95..<16 * 95 + 16}"
  then have "j \<in> set [1520..<1536]" unfolding set_upt by simp
  then have "j \<in> set [1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535]" unfolding gupt_nc_095 .
  then show "gdc_sub None j" using gdc_nc_1520 gdc_nc_1521 gdc_nc_1522 gdc_nc_1523 gdc_nc_1524 gdc_nc_1525 gdc_nc_1526 gdc_nc_1527 gdc_nc_1528 gdc_nc_1529 gdc_nc_1530 gdc_nc_1531 gdc_nc_1532 gdc_nc_1533 gdc_nc_1534 gdc_nc_1535
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
