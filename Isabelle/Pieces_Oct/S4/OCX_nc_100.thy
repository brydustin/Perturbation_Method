theory OCX_nc_100
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1600: "oc_sub None 1600"
  by (oc_eval oc_nc_1600)

lemma oc_nc_1601: "oc_sub None 1601"
  by (oc_eval oc_nc_1601)

lemma oc_nc_1602: "oc_sub None 1602"
  by (oc_eval oc_nc_1602)

lemma oc_nc_1603: "oc_sub None 1603"
  by (oc_eval oc_nc_1603)

lemma oc_nc_1604: "oc_sub None 1604"
  by (oc_eval oc_nc_1604)

lemma oc_nc_1605: "oc_sub None 1605"
  by (oc_eval oc_nc_1605)

lemma oc_nc_1606: "oc_sub None 1606"
  by (oc_eval oc_nc_1606)

lemma oc_nc_1607: "oc_sub None 1607"
  by (oc_eval oc_nc_1607)

lemma oc_nc_1608: "oc_sub None 1608"
  by (oc_eval oc_nc_1608)

lemma oc_nc_1609: "oc_sub None 1609"
  by (oc_eval oc_nc_1609)

lemma oc_nc_1610: "oc_sub None 1610"
  by (oc_eval oc_nc_1610)

lemma oc_nc_1611: "oc_sub None 1611"
  by (oc_eval oc_nc_1611)

lemma oc_nc_1612: "oc_sub None 1612"
  by (oc_eval oc_nc_1612)

lemma oc_nc_1613: "oc_sub None 1613"
  by (oc_eval oc_nc_1613)

lemma oc_nc_1614: "oc_sub None 1614"
  by (oc_eval oc_nc_1614)

lemma oc_nc_1615: "oc_sub None 1615"
  by (oc_eval oc_nc_1615)

lemma upt_nc_100: "[1600..<1616] = [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]"
  by (simp add: upt_rec)

lemma sec_nc_100: "\<forall>j\<in>{16 * 100..<16 * 100 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 100..<16 * 100 + 16}"
  then have "j \<in> set [1600..<1616]" unfolding set_upt by simp
  then have "j \<in> set [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]" unfolding upt_nc_100 .
  then show "oc_sub None j" using oc_nc_1600 oc_nc_1601 oc_nc_1602 oc_nc_1603 oc_nc_1604 oc_nc_1605 oc_nc_1606 oc_nc_1607 oc_nc_1608 oc_nc_1609 oc_nc_1610 oc_nc_1611 oc_nc_1612 oc_nc_1613 oc_nc_1614 oc_nc_1615
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
