theory DCX_nc_100
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1600: "dc_sub None 1600"
  by (dc_eval dc_nc_1600)

lemma dc_nc_1601: "dc_sub None 1601"
  by (dc_eval dc_nc_1601)

lemma dc_nc_1602: "dc_sub None 1602"
  by (dc_eval dc_nc_1602)

lemma dc_nc_1603: "dc_sub None 1603"
  by (dc_eval dc_nc_1603)

lemma dc_nc_1604: "dc_sub None 1604"
  by (dc_eval dc_nc_1604)

lemma dc_nc_1605: "dc_sub None 1605"
  by (dc_eval dc_nc_1605)

lemma dc_nc_1606: "dc_sub None 1606"
  by (dc_eval dc_nc_1606)

lemma dc_nc_1607: "dc_sub None 1607"
  by (dc_eval dc_nc_1607)

lemma dc_nc_1608: "dc_sub None 1608"
  by (dc_eval dc_nc_1608)

lemma dc_nc_1609: "dc_sub None 1609"
  by (dc_eval dc_nc_1609)

lemma dc_nc_1610: "dc_sub None 1610"
  by (dc_eval dc_nc_1610)

lemma dc_nc_1611: "dc_sub None 1611"
  by (dc_eval dc_nc_1611)

lemma dc_nc_1612: "dc_sub None 1612"
  by (dc_eval dc_nc_1612)

lemma dc_nc_1613: "dc_sub None 1613"
  by (dc_eval dc_nc_1613)

lemma dc_nc_1614: "dc_sub None 1614"
  by (dc_eval dc_nc_1614)

lemma dc_nc_1615: "dc_sub None 1615"
  by (dc_eval dc_nc_1615)

lemma upt_nc_100: "[1600..<1616] = [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]"
  by (simp add: upt_rec)

lemma sec_nc_100: "\<forall>j\<in>{16 * 100..<16 * 100 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 100..<16 * 100 + 16}"
  then have "j \<in> set [1600..<1616]" unfolding set_upt by simp
  then have "j \<in> set [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]" unfolding upt_nc_100 .
  then show "dc_sub None j" using dc_nc_1600 dc_nc_1601 dc_nc_1602 dc_nc_1603 dc_nc_1604 dc_nc_1605 dc_nc_1606 dc_nc_1607 dc_nc_1608 dc_nc_1609 dc_nc_1610 dc_nc_1611 dc_nc_1612 dc_nc_1613 dc_nc_1614 dc_nc_1615
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
