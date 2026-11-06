theory DCX_c30_098
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1568: "dc_sub dc_b30 1568"
  by (dc_eval dc_c30_1568)

lemma dc_c30_1569: "dc_sub dc_b30 1569"
  by (dc_eval dc_c30_1569)

lemma dc_c30_1570: "dc_sub dc_b30 1570"
  by (dc_eval dc_c30_1570)

lemma dc_c30_1571: "dc_sub dc_b30 1571"
  by (dc_eval dc_c30_1571)

lemma dc_c30_1572: "dc_sub dc_b30 1572"
  by (dc_eval dc_c30_1572)

lemma dc_c30_1573: "dc_sub dc_b30 1573"
  by (dc_eval dc_c30_1573)

lemma dc_c30_1574: "dc_sub dc_b30 1574"
  by (dc_eval dc_c30_1574)

lemma dc_c30_1575: "dc_sub dc_b30 1575"
  by (dc_eval dc_c30_1575)

lemma dc_c30_1576: "dc_sub dc_b30 1576"
  by (dc_eval dc_c30_1576)

lemma dc_c30_1577: "dc_sub dc_b30 1577"
  by (dc_eval dc_c30_1577)

lemma dc_c30_1578: "dc_sub dc_b30 1578"
  by (dc_eval dc_c30_1578)

lemma dc_c30_1579: "dc_sub dc_b30 1579"
  by (dc_eval dc_c30_1579)

lemma dc_c30_1580: "dc_sub dc_b30 1580"
  by (dc_eval dc_c30_1580)

lemma dc_c30_1581: "dc_sub dc_b30 1581"
  by (dc_eval dc_c30_1581)

lemma dc_c30_1582: "dc_sub dc_b30 1582"
  by (dc_eval dc_c30_1582)

lemma dc_c30_1583: "dc_sub dc_b30 1583"
  by (dc_eval dc_c30_1583)

lemma upt_c30_098: "[1568..<1584] = [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]"
  by (simp add: upt_rec)

lemma sec_c30_098: "\<forall>j\<in>{16 * 98..<16 * 98 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 98..<16 * 98 + 16}"
  then have "j \<in> set [1568..<1584]" unfolding set_upt by simp
  then have "j \<in> set [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]" unfolding upt_c30_098 .
  then show "dc_sub dc_b30 j" using dc_c30_1568 dc_c30_1569 dc_c30_1570 dc_c30_1571 dc_c30_1572 dc_c30_1573 dc_c30_1574 dc_c30_1575 dc_c30_1576 dc_c30_1577 dc_c30_1578 dc_c30_1579 dc_c30_1580 dc_c30_1581 dc_c30_1582 dc_c30_1583
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
