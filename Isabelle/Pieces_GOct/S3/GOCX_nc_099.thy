theory GOCX_nc_099
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1584: "goc_sub None 1584"
  by (goc_eval goc_nc_1584)

lemma goc_nc_1585: "goc_sub None 1585"
  by (goc_eval goc_nc_1585)

lemma goc_nc_1586: "goc_sub None 1586"
  by (goc_eval goc_nc_1586)

lemma goc_nc_1587: "goc_sub None 1587"
  by (goc_eval goc_nc_1587)

lemma goc_nc_1588: "goc_sub None 1588"
  by (goc_eval goc_nc_1588)

lemma goc_nc_1589: "goc_sub None 1589"
  by (goc_eval goc_nc_1589)

lemma goc_nc_1590: "goc_sub None 1590"
  by (goc_eval goc_nc_1590)

lemma goc_nc_1591: "goc_sub None 1591"
  by (goc_eval goc_nc_1591)

lemma goc_nc_1592: "goc_sub None 1592"
  by (goc_eval goc_nc_1592)

lemma goc_nc_1593: "goc_sub None 1593"
  by (goc_eval goc_nc_1593)

lemma goc_nc_1594: "goc_sub None 1594"
  by (goc_eval goc_nc_1594)

lemma goc_nc_1595: "goc_sub None 1595"
  by (goc_eval goc_nc_1595)

lemma goc_nc_1596: "goc_sub None 1596"
  by (goc_eval goc_nc_1596)

lemma goc_nc_1597: "goc_sub None 1597"
  by (goc_eval goc_nc_1597)

lemma goc_nc_1598: "goc_sub None 1598"
  by (goc_eval goc_nc_1598)

lemma goc_nc_1599: "goc_sub None 1599"
  by (goc_eval goc_nc_1599)

lemma gupt_nc_099: "[1584..<1600] = [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]"
  by (simp add: upt_rec)

lemma gsec_nc_099: "\<forall>j\<in>{16 * 99..<16 * 99 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 99..<16 * 99 + 16}"
  then have "j \<in> set [1584..<1600]" unfolding set_upt by simp
  then have "j \<in> set [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]" unfolding gupt_nc_099 .
  then show "goc_sub None j" using goc_nc_1584 goc_nc_1585 goc_nc_1586 goc_nc_1587 goc_nc_1588 goc_nc_1589 goc_nc_1590 goc_nc_1591 goc_nc_1592 goc_nc_1593 goc_nc_1594 goc_nc_1595 goc_nc_1596 goc_nc_1597 goc_nc_1598 goc_nc_1599
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
