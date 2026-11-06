theory GOCX_nc_100
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1600: "goc_sub None 1600"
  by (goc_eval goc_nc_1600)

lemma goc_nc_1601: "goc_sub None 1601"
  by (goc_eval goc_nc_1601)

lemma goc_nc_1602: "goc_sub None 1602"
  by (goc_eval goc_nc_1602)

lemma goc_nc_1603: "goc_sub None 1603"
  by (goc_eval goc_nc_1603)

lemma goc_nc_1604: "goc_sub None 1604"
  by (goc_eval goc_nc_1604)

lemma goc_nc_1605: "goc_sub None 1605"
  by (goc_eval goc_nc_1605)

lemma goc_nc_1606: "goc_sub None 1606"
  by (goc_eval goc_nc_1606)

lemma goc_nc_1607: "goc_sub None 1607"
  by (goc_eval goc_nc_1607)

lemma goc_nc_1608: "goc_sub None 1608"
  by (goc_eval goc_nc_1608)

lemma goc_nc_1609: "goc_sub None 1609"
  by (goc_eval goc_nc_1609)

lemma goc_nc_1610: "goc_sub None 1610"
  by (goc_eval goc_nc_1610)

lemma goc_nc_1611: "goc_sub None 1611"
  by (goc_eval goc_nc_1611)

lemma goc_nc_1612: "goc_sub None 1612"
  by (goc_eval goc_nc_1612)

lemma goc_nc_1613: "goc_sub None 1613"
  by (goc_eval goc_nc_1613)

lemma goc_nc_1614: "goc_sub None 1614"
  by (goc_eval goc_nc_1614)

lemma goc_nc_1615: "goc_sub None 1615"
  by (goc_eval goc_nc_1615)

lemma gupt_nc_100: "[1600..<1616] = [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]"
  by (simp add: upt_rec)

lemma gsec_nc_100: "\<forall>j\<in>{16 * 100..<16 * 100 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 100..<16 * 100 + 16}"
  then have "j \<in> set [1600..<1616]" unfolding set_upt by simp
  then have "j \<in> set [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]" unfolding gupt_nc_100 .
  then show "goc_sub None j" using goc_nc_1600 goc_nc_1601 goc_nc_1602 goc_nc_1603 goc_nc_1604 goc_nc_1605 goc_nc_1606 goc_nc_1607 goc_nc_1608 goc_nc_1609 goc_nc_1610 goc_nc_1611 goc_nc_1612 goc_nc_1613 goc_nc_1614 goc_nc_1615
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
