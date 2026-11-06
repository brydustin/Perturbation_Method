theory GDCX_nc_100
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1600: "gdc_sub None 1600"
  by (gdc_eval gdc_nc_1600)

lemma gdc_nc_1601: "gdc_sub None 1601"
  by (gdc_eval gdc_nc_1601)

lemma gdc_nc_1602: "gdc_sub None 1602"
  by (gdc_eval gdc_nc_1602)

lemma gdc_nc_1603: "gdc_sub None 1603"
  by (gdc_eval gdc_nc_1603)

lemma gdc_nc_1604: "gdc_sub None 1604"
  by (gdc_eval gdc_nc_1604)

lemma gdc_nc_1605: "gdc_sub None 1605"
  by (gdc_eval gdc_nc_1605)

lemma gdc_nc_1606: "gdc_sub None 1606"
  by (gdc_eval gdc_nc_1606)

lemma gdc_nc_1607: "gdc_sub None 1607"
  by (gdc_eval gdc_nc_1607)

lemma gdc_nc_1608: "gdc_sub None 1608"
  by (gdc_eval gdc_nc_1608)

lemma gdc_nc_1609: "gdc_sub None 1609"
  by (gdc_eval gdc_nc_1609)

lemma gdc_nc_1610: "gdc_sub None 1610"
  by (gdc_eval gdc_nc_1610)

lemma gdc_nc_1611: "gdc_sub None 1611"
  by (gdc_eval gdc_nc_1611)

lemma gdc_nc_1612: "gdc_sub None 1612"
  by (gdc_eval gdc_nc_1612)

lemma gdc_nc_1613: "gdc_sub None 1613"
  by (gdc_eval gdc_nc_1613)

lemma gdc_nc_1614: "gdc_sub None 1614"
  by (gdc_eval gdc_nc_1614)

lemma gdc_nc_1615: "gdc_sub None 1615"
  by (gdc_eval gdc_nc_1615)

lemma gupt_nc_100: "[1600..<1616] = [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]"
  by (simp add: upt_rec)

lemma gsec_nc_100: "\<forall>j\<in>{16 * 100..<16 * 100 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 100..<16 * 100 + 16}"
  then have "j \<in> set [1600..<1616]" unfolding set_upt by simp
  then have "j \<in> set [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]" unfolding gupt_nc_100 .
  then show "gdc_sub None j" using gdc_nc_1600 gdc_nc_1601 gdc_nc_1602 gdc_nc_1603 gdc_nc_1604 gdc_nc_1605 gdc_nc_1606 gdc_nc_1607 gdc_nc_1608 gdc_nc_1609 gdc_nc_1610 gdc_nc_1611 gdc_nc_1612 gdc_nc_1613 gdc_nc_1614 gdc_nc_1615
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
