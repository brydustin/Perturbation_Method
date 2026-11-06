theory GDCX_nc_098
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1568: "gdc_sub None 1568"
  by (gdc_eval gdc_nc_1568)

lemma gdc_nc_1569: "gdc_sub None 1569"
  by (gdc_eval gdc_nc_1569)

lemma gdc_nc_1570: "gdc_sub None 1570"
  by (gdc_eval gdc_nc_1570)

lemma gdc_nc_1571: "gdc_sub None 1571"
  by (gdc_eval gdc_nc_1571)

lemma gdc_nc_1572: "gdc_sub None 1572"
  by (gdc_eval gdc_nc_1572)

lemma gdc_nc_1573: "gdc_sub None 1573"
  by (gdc_eval gdc_nc_1573)

lemma gdc_nc_1574: "gdc_sub None 1574"
  by (gdc_eval gdc_nc_1574)

lemma gdc_nc_1575: "gdc_sub None 1575"
  by (gdc_eval gdc_nc_1575)

lemma gdc_nc_1576: "gdc_sub None 1576"
  by (gdc_eval gdc_nc_1576)

lemma gdc_nc_1577: "gdc_sub None 1577"
  by (gdc_eval gdc_nc_1577)

lemma gdc_nc_1578: "gdc_sub None 1578"
  by (gdc_eval gdc_nc_1578)

lemma gdc_nc_1579: "gdc_sub None 1579"
  by (gdc_eval gdc_nc_1579)

lemma gdc_nc_1580: "gdc_sub None 1580"
  by (gdc_eval gdc_nc_1580)

lemma gdc_nc_1581: "gdc_sub None 1581"
  by (gdc_eval gdc_nc_1581)

lemma gdc_nc_1582: "gdc_sub None 1582"
  by (gdc_eval gdc_nc_1582)

lemma gdc_nc_1583: "gdc_sub None 1583"
  by (gdc_eval gdc_nc_1583)

lemma gupt_nc_098: "[1568..<1584] = [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]"
  by (simp add: upt_rec)

lemma gsec_nc_098: "\<forall>j\<in>{16 * 98..<16 * 98 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 98..<16 * 98 + 16}"
  then have "j \<in> set [1568..<1584]" unfolding set_upt by simp
  then have "j \<in> set [1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583]" unfolding gupt_nc_098 .
  then show "gdc_sub None j" using gdc_nc_1568 gdc_nc_1569 gdc_nc_1570 gdc_nc_1571 gdc_nc_1572 gdc_nc_1573 gdc_nc_1574 gdc_nc_1575 gdc_nc_1576 gdc_nc_1577 gdc_nc_1578 gdc_nc_1579 gdc_nc_1580 gdc_nc_1581 gdc_nc_1582 gdc_nc_1583
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
