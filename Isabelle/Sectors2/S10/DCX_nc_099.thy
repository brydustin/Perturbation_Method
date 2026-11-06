theory DCX_nc_099
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1584: "dc_sub None 1584"
  by (dc_eval dc_nc_1584)

lemma dc_nc_1585: "dc_sub None 1585"
  by (dc_eval dc_nc_1585)

lemma dc_nc_1586: "dc_sub None 1586"
  by (dc_eval dc_nc_1586)

lemma dc_nc_1587: "dc_sub None 1587"
  by (dc_eval dc_nc_1587)

lemma dc_nc_1588: "dc_sub None 1588"
  by (dc_eval dc_nc_1588)

lemma dc_nc_1589: "dc_sub None 1589"
  by (dc_eval dc_nc_1589)

lemma dc_nc_1590: "dc_sub None 1590"
  by (dc_eval dc_nc_1590)

lemma dc_nc_1591: "dc_sub None 1591"
  by (dc_eval dc_nc_1591)

lemma dc_nc_1592: "dc_sub None 1592"
  by (dc_eval dc_nc_1592)

lemma dc_nc_1593: "dc_sub None 1593"
  by (dc_eval dc_nc_1593)

lemma dc_nc_1594: "dc_sub None 1594"
  by (dc_eval dc_nc_1594)

lemma dc_nc_1595: "dc_sub None 1595"
  by (dc_eval dc_nc_1595)

lemma dc_nc_1596: "dc_sub None 1596"
  by (dc_eval dc_nc_1596)

lemma dc_nc_1597: "dc_sub None 1597"
  by (dc_eval dc_nc_1597)

lemma dc_nc_1598: "dc_sub None 1598"
  by (dc_eval dc_nc_1598)

lemma dc_nc_1599: "dc_sub None 1599"
  by (dc_eval dc_nc_1599)

lemma upt_nc_099: "[1584..<1600] = [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]"
  by (simp add: upt_rec)

lemma sec_nc_099: "\<forall>j\<in>{16 * 99..<16 * 99 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 99..<16 * 99 + 16}"
  then have "j \<in> set [1584..<1600]" unfolding set_upt by simp
  then have "j \<in> set [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]" unfolding upt_nc_099 .
  then show "dc_sub None j" using dc_nc_1584 dc_nc_1585 dc_nc_1586 dc_nc_1587 dc_nc_1588 dc_nc_1589 dc_nc_1590 dc_nc_1591 dc_nc_1592 dc_nc_1593 dc_nc_1594 dc_nc_1595 dc_nc_1596 dc_nc_1597 dc_nc_1598 dc_nc_1599
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
