theory OCX_nc_099
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1584: "oc_sub None 1584"
  by (oc_eval oc_nc_1584)

lemma oc_nc_1585: "oc_sub None 1585"
  by (oc_eval oc_nc_1585)

lemma oc_nc_1586: "oc_sub None 1586"
  by (oc_eval oc_nc_1586)

lemma oc_nc_1587: "oc_sub None 1587"
  by (oc_eval oc_nc_1587)

lemma oc_nc_1588: "oc_sub None 1588"
  by (oc_eval oc_nc_1588)

lemma oc_nc_1589: "oc_sub None 1589"
  by (oc_eval oc_nc_1589)

lemma oc_nc_1590: "oc_sub None 1590"
  by (oc_eval oc_nc_1590)

lemma oc_nc_1591: "oc_sub None 1591"
  by (oc_eval oc_nc_1591)

lemma oc_nc_1592: "oc_sub None 1592"
  by (oc_eval oc_nc_1592)

lemma oc_nc_1593: "oc_sub None 1593"
  by (oc_eval oc_nc_1593)

lemma oc_nc_1594: "oc_sub None 1594"
  by (oc_eval oc_nc_1594)

lemma oc_nc_1595: "oc_sub None 1595"
  by (oc_eval oc_nc_1595)

lemma oc_nc_1596: "oc_sub None 1596"
  by (oc_eval oc_nc_1596)

lemma oc_nc_1597: "oc_sub None 1597"
  by (oc_eval oc_nc_1597)

lemma oc_nc_1598: "oc_sub None 1598"
  by (oc_eval oc_nc_1598)

lemma oc_nc_1599: "oc_sub None 1599"
  by (oc_eval oc_nc_1599)

lemma upt_nc_099: "[1584..<1600] = [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]"
  by (simp add: upt_rec)

lemma sec_nc_099: "\<forall>j\<in>{16 * 99..<16 * 99 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 99..<16 * 99 + 16}"
  then have "j \<in> set [1584..<1600]" unfolding set_upt by simp
  then have "j \<in> set [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]" unfolding upt_nc_099 .
  then show "oc_sub None j" using oc_nc_1584 oc_nc_1585 oc_nc_1586 oc_nc_1587 oc_nc_1588 oc_nc_1589 oc_nc_1590 oc_nc_1591 oc_nc_1592 oc_nc_1593 oc_nc_1594 oc_nc_1595 oc_nc_1596 oc_nc_1597 oc_nc_1598 oc_nc_1599
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
