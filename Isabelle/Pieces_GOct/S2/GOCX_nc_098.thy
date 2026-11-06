theory GOCX_nc_098
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1568: "goc_sub None 1568"
  by (goc_eval goc_nc_1568)

lemma goc_nc_1569: "goc_sub None 1569"
  by (goc_eval goc_nc_1569)

lemma goc_nc_1570: "goc_sub None 1570"
  by (goc_eval goc_nc_1570)

lemma goc_nc_1571: "goc_sub None 1571"
  by (goc_eval goc_nc_1571)

lemma goc_nc_1572: "goc_sub None 1572"
  by (goc_eval goc_nc_1572)

lemma goc_nc_1573: "goc_sub None 1573"
  by (goc_eval goc_nc_1573)

lemma goc_nc_1574: "goc_sub None 1574"
  by (goc_eval goc_nc_1574)

lemma goc_nc_1575: "goc_sub None 1575"
  by (goc_eval goc_nc_1575)

lemma goc_nc_1576: "goc_sub None 1576"
  by (goc_eval goc_nc_1576)

lemma goc_nc_1577: "goc_sub None 1577"
  by (goc_eval goc_nc_1577)

lemma goc_nc_1578: "goc_sub None 1578"
  by (goc_eval goc_nc_1578)

lemma goc_nc_1579: "goc_sub None 1579"
  by (goc_eval goc_nc_1579)

lemma goc_nc_1580: "goc_sub None 1580"
  by (goc_eval goc_nc_1580)

lemma goc_nc_1581: "goc_sub None 1581"
  by (goc_eval goc_nc_1581)

lemma goc_nc_1582: "goc_sub None 1582"
  by (goc_eval goc_nc_1582)

lemma goc_nc_1583: "goc_sub None 1583"
  by (goc_eval goc_nc_1583)

lemma gupt_nc_098: "[1568..<1584] = [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]"
  by (simp add: upt_rec)

lemma gsec_nc_098: "\<forall>j\<in>{16 * 98..<16 * 98 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 98..<16 * 98 + 16}"
  then have "j \<in> set [1568..<1584]" unfolding set_upt by simp
  then have "j \<in> set [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]" unfolding gupt_nc_098 .
  then show "goc_sub None j" using goc_nc_1568 goc_nc_1569 goc_nc_1570 goc_nc_1571 goc_nc_1572 goc_nc_1573 goc_nc_1574 goc_nc_1575 goc_nc_1576 goc_nc_1577 goc_nc_1578 goc_nc_1579 goc_nc_1580 goc_nc_1581 goc_nc_1582 goc_nc_1583
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
