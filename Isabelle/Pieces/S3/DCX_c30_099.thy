theory DCX_c30_099
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1584: "dc_sub dc_b30 1584"
  by (dc_eval dc_c30_1584)

lemma dc_c30_1585: "dc_sub dc_b30 1585"
  by (dc_eval dc_c30_1585)

lemma dc_c30_1586: "dc_sub dc_b30 1586"
  by (dc_eval dc_c30_1586)

lemma dc_c30_1587: "dc_sub dc_b30 1587"
  by (dc_eval dc_c30_1587)

lemma dc_c30_1588: "dc_sub dc_b30 1588"
  by (dc_eval dc_c30_1588)

lemma dc_c30_1589: "dc_sub dc_b30 1589"
  by (dc_eval dc_c30_1589)

lemma dc_c30_1590: "dc_sub dc_b30 1590"
  by (dc_eval dc_c30_1590)

lemma dc_c30_1591: "dc_sub dc_b30 1591"
  by (dc_eval dc_c30_1591)

lemma dc_c30_1592: "dc_sub dc_b30 1592"
  by (dc_eval dc_c30_1592)

lemma dc_c30_1593: "dc_sub dc_b30 1593"
  by (dc_eval dc_c30_1593)

lemma dc_c30_1594: "dc_sub dc_b30 1594"
  by (dc_eval dc_c30_1594)

lemma dc_c30_1595: "dc_sub dc_b30 1595"
  by (dc_eval dc_c30_1595)

lemma dc_c30_1596: "dc_sub dc_b30 1596"
  by (dc_eval dc_c30_1596)

lemma dc_c30_1597: "dc_sub dc_b30 1597"
  by (dc_eval dc_c30_1597)

lemma dc_c30_1598: "dc_sub dc_b30 1598"
  by (dc_eval dc_c30_1598)

lemma dc_c30_1599: "dc_sub dc_b30 1599"
  by (dc_eval dc_c30_1599)

lemma upt_c30_099: "[1584..<1600] = [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]"
  by (simp add: upt_rec)

lemma sec_c30_099: "\<forall>j\<in>{16 * 99..<16 * 99 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 99..<16 * 99 + 16}"
  then have "j \<in> set [1584..<1600]" unfolding set_upt by simp
  then have "j \<in> set [1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599]" unfolding upt_c30_099 .
  then show "dc_sub dc_b30 j" using dc_c30_1584 dc_c30_1585 dc_c30_1586 dc_c30_1587 dc_c30_1588 dc_c30_1589 dc_c30_1590 dc_c30_1591 dc_c30_1592 dc_c30_1593 dc_c30_1594 dc_c30_1595 dc_c30_1596 dc_c30_1597 dc_c30_1598 dc_c30_1599
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
