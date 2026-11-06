theory DCX_c30_101
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1616: "dc_sub dc_b30 1616"
  by (dc_eval dc_c30_1616)

lemma dc_c30_1617: "dc_sub dc_b30 1617"
  by (dc_eval dc_c30_1617)

lemma dc_c30_1618: "dc_sub dc_b30 1618"
  by (dc_eval dc_c30_1618)

lemma dc_c30_1619: "dc_sub dc_b30 1619"
  by (dc_eval dc_c30_1619)

lemma dc_c30_1620: "dc_sub dc_b30 1620"
  by (dc_eval dc_c30_1620)

lemma dc_c30_1621: "dc_sub dc_b30 1621"
  by (dc_eval dc_c30_1621)

lemma dc_c30_1622: "dc_sub dc_b30 1622"
  by (dc_eval dc_c30_1622)

lemma dc_c30_1623: "dc_sub dc_b30 1623"
  by (dc_eval dc_c30_1623)

lemma dc_c30_1624: "dc_sub dc_b30 1624"
  by (dc_eval dc_c30_1624)

lemma dc_c30_1625: "dc_sub dc_b30 1625"
  by (dc_eval dc_c30_1625)

lemma dc_c30_1626: "dc_sub dc_b30 1626"
  by (dc_eval dc_c30_1626)

lemma dc_c30_1627: "dc_sub dc_b30 1627"
  by (dc_eval dc_c30_1627)

lemma dc_c30_1628: "dc_sub dc_b30 1628"
  by (dc_eval dc_c30_1628)

lemma dc_c30_1629: "dc_sub dc_b30 1629"
  by (dc_eval dc_c30_1629)

lemma dc_c30_1630: "dc_sub dc_b30 1630"
  by (dc_eval dc_c30_1630)

lemma dc_c30_1631: "dc_sub dc_b30 1631"
  by (dc_eval dc_c30_1631)

lemma upt_c30_101: "[1616..<1632] = [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]"
  by (simp add: upt_rec)

lemma sec_c30_101: "\<forall>j\<in>{16 * 101..<16 * 101 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 101..<16 * 101 + 16}"
  then have "j \<in> set [1616..<1632]" unfolding set_upt by simp
  then have "j \<in> set [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]" unfolding upt_c30_101 .
  then show "dc_sub dc_b30 j" using dc_c30_1616 dc_c30_1617 dc_c30_1618 dc_c30_1619 dc_c30_1620 dc_c30_1621 dc_c30_1622 dc_c30_1623 dc_c30_1624 dc_c30_1625 dc_c30_1626 dc_c30_1627 dc_c30_1628 dc_c30_1629 dc_c30_1630 dc_c30_1631
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
