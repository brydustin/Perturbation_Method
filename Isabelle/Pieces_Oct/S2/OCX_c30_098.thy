theory OCX_c30_098
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1568: "oc_sub oc_b30 1568"
  by (oc_eval oc_c30_1568)

lemma oc_c30_1569: "oc_sub oc_b30 1569"
  by (oc_eval oc_c30_1569)

lemma oc_c30_1570: "oc_sub oc_b30 1570"
  by (oc_eval oc_c30_1570)

lemma oc_c30_1571: "oc_sub oc_b30 1571"
  by (oc_eval oc_c30_1571)

lemma oc_c30_1572: "oc_sub oc_b30 1572"
  by (oc_eval oc_c30_1572)

lemma oc_c30_1573: "oc_sub oc_b30 1573"
  by (oc_eval oc_c30_1573)

lemma oc_c30_1574: "oc_sub oc_b30 1574"
  by (oc_eval oc_c30_1574)

lemma oc_c30_1575: "oc_sub oc_b30 1575"
  by (oc_eval oc_c30_1575)

lemma oc_c30_1576: "oc_sub oc_b30 1576"
  by (oc_eval oc_c30_1576)

lemma oc_c30_1577: "oc_sub oc_b30 1577"
  by (oc_eval oc_c30_1577)

lemma oc_c30_1578: "oc_sub oc_b30 1578"
  by (oc_eval oc_c30_1578)

lemma oc_c30_1579: "oc_sub oc_b30 1579"
  by (oc_eval oc_c30_1579)

lemma oc_c30_1580: "oc_sub oc_b30 1580"
  by (oc_eval oc_c30_1580)

lemma oc_c30_1581: "oc_sub oc_b30 1581"
  by (oc_eval oc_c30_1581)

lemma oc_c30_1582: "oc_sub oc_b30 1582"
  by (oc_eval oc_c30_1582)

lemma oc_c30_1583: "oc_sub oc_b30 1583"
  by (oc_eval oc_c30_1583)

lemma upt_c30_098: "[1568..<1584] = [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]"
  by (simp add: upt_rec)

lemma sec_c30_098: "\<forall>j\<in>{16 * 98..<16 * 98 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 98..<16 * 98 + 16}"
  then have "j \<in> set [1568..<1584]" unfolding set_upt by simp
  then have "j \<in> set [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]" unfolding upt_c30_098 .
  then show "oc_sub oc_b30 j" using oc_c30_1568 oc_c30_1569 oc_c30_1570 oc_c30_1571 oc_c30_1572 oc_c30_1573 oc_c30_1574 oc_c30_1575 oc_c30_1576 oc_c30_1577 oc_c30_1578 oc_c30_1579 oc_c30_1580 oc_c30_1581 oc_c30_1582 oc_c30_1583
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
