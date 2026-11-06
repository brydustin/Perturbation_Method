theory OCX_c30_100
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1600: "oc_sub oc_b30 1600"
  by (oc_eval oc_c30_1600)

lemma oc_c30_1601: "oc_sub oc_b30 1601"
  by (oc_eval oc_c30_1601)

lemma oc_c30_1602: "oc_sub oc_b30 1602"
  by (oc_eval oc_c30_1602)

lemma oc_c30_1603: "oc_sub oc_b30 1603"
  by (oc_eval oc_c30_1603)

lemma oc_c30_1604: "oc_sub oc_b30 1604"
  by (oc_eval oc_c30_1604)

lemma oc_c30_1605: "oc_sub oc_b30 1605"
  by (oc_eval oc_c30_1605)

lemma oc_c30_1606: "oc_sub oc_b30 1606"
  by (oc_eval oc_c30_1606)

lemma oc_c30_1607: "oc_sub oc_b30 1607"
  by (oc_eval oc_c30_1607)

lemma oc_c30_1608: "oc_sub oc_b30 1608"
  by (oc_eval oc_c30_1608)

lemma oc_c30_1609: "oc_sub oc_b30 1609"
  by (oc_eval oc_c30_1609)

lemma oc_c30_1610: "oc_sub oc_b30 1610"
  by (oc_eval oc_c30_1610)

lemma oc_c30_1611: "oc_sub oc_b30 1611"
  by (oc_eval oc_c30_1611)

lemma oc_c30_1612: "oc_sub oc_b30 1612"
  by (oc_eval oc_c30_1612)

lemma oc_c30_1613: "oc_sub oc_b30 1613"
  by (oc_eval oc_c30_1613)

lemma oc_c30_1614: "oc_sub oc_b30 1614"
  by (oc_eval oc_c30_1614)

lemma oc_c30_1615: "oc_sub oc_b30 1615"
  by (oc_eval oc_c30_1615)

lemma upt_c30_100: "[1600..<1616] = [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]"
  by (simp add: upt_rec)

lemma sec_c30_100: "\<forall>j\<in>{16 * 100..<16 * 100 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 100..<16 * 100 + 16}"
  then have "j \<in> set [1600..<1616]" unfolding set_upt by simp
  then have "j \<in> set [1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615]" unfolding upt_c30_100 .
  then show "oc_sub oc_b30 j" using oc_c30_1600 oc_c30_1601 oc_c30_1602 oc_c30_1603 oc_c30_1604 oc_c30_1605 oc_c30_1606 oc_c30_1607 oc_c30_1608 oc_c30_1609 oc_c30_1610 oc_c30_1611 oc_c30_1612 oc_c30_1613 oc_c30_1614 oc_c30_1615
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
