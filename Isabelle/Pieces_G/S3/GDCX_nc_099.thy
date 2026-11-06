theory GDCX_nc_099
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1584: "gdc_sub None 1584"
  by (gdc_eval gdc_nc_1584)

lemma gdc_nc_1585: "gdc_sub None 1585"
  by (gdc_eval gdc_nc_1585)

lemma gdc_nc_1586: "gdc_sub None 1586"
  by (gdc_eval gdc_nc_1586)

lemma gdc_nc_1587: "gdc_sub None 1587"
  by (gdc_eval gdc_nc_1587)

lemma gdc_nc_1588: "gdc_sub None 1588"
  by (gdc_eval gdc_nc_1588)

lemma gdc_nc_1589: "gdc_sub None 1589"
  by (gdc_eval gdc_nc_1589)

lemma gdc_nc_1590: "gdc_sub None 1590"
  by (gdc_eval gdc_nc_1590)

lemma gdc_nc_1591: "gdc_sub None 1591"
  by (gdc_eval gdc_nc_1591)

lemma gdc_nc_1592: "gdc_sub None 1592"
  by (gdc_eval gdc_nc_1592)

lemma gdc_nc_1593: "gdc_sub None 1593"
  by (gdc_eval gdc_nc_1593)

lemma gdc_nc_1594: "gdc_sub None 1594"
  by (gdc_eval gdc_nc_1594)

lemma gdc_nc_1595: "gdc_sub None 1595"
  by (gdc_eval gdc_nc_1595)

lemma gdc_nc_1596: "gdc_sub None 1596"
  by (gdc_eval gdc_nc_1596)

lemma gdc_nc_1597: "gdc_sub None 1597"
  by (gdc_eval gdc_nc_1597)

lemma gdc_nc_1598: "gdc_sub None 1598"
  by (gdc_eval gdc_nc_1598)

lemma gdc_nc_1599: "gdc_sub None 1599"
  by (gdc_eval gdc_nc_1599)

lemma gupt_nc_099: "[1584..<1600] = [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]"
  by (simp add: upt_rec)

lemma gsec_nc_099: "\<forall>j\<in>{16 * 99..<16 * 99 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 99..<16 * 99 + 16}"
  then have "j \<in> set [1584..<1600]" unfolding set_upt by simp
  then have "j \<in> set [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]" unfolding gupt_nc_099 .
  then show "gdc_sub None j" using gdc_nc_1584 gdc_nc_1585 gdc_nc_1586 gdc_nc_1587 gdc_nc_1588 gdc_nc_1589 gdc_nc_1590 gdc_nc_1591 gdc_nc_1592 gdc_nc_1593 gdc_nc_1594 gdc_nc_1595 gdc_nc_1596 gdc_nc_1597 gdc_nc_1598 gdc_nc_1599
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
