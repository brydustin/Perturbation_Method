theory DCX_nc_101
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1616: "dc_sub None 1616"
  by (dc_eval dc_nc_1616)

lemma dc_nc_1617: "dc_sub None 1617"
  by (dc_eval dc_nc_1617)

lemma dc_nc_1618: "dc_sub None 1618"
  by (dc_eval dc_nc_1618)

lemma dc_nc_1619: "dc_sub None 1619"
  by (dc_eval dc_nc_1619)

lemma dc_nc_1620: "dc_sub None 1620"
  by (dc_eval dc_nc_1620)

lemma dc_nc_1621: "dc_sub None 1621"
  by (dc_eval dc_nc_1621)

lemma dc_nc_1622: "dc_sub None 1622"
  by (dc_eval dc_nc_1622)

lemma dc_nc_1623: "dc_sub None 1623"
  by (dc_eval dc_nc_1623)

lemma dc_nc_1624: "dc_sub None 1624"
  by (dc_eval dc_nc_1624)

lemma dc_nc_1625: "dc_sub None 1625"
  by (dc_eval dc_nc_1625)

lemma dc_nc_1626: "dc_sub None 1626"
  by (dc_eval dc_nc_1626)

lemma dc_nc_1627: "dc_sub None 1627"
  by (dc_eval dc_nc_1627)

lemma dc_nc_1628: "dc_sub None 1628"
  by (dc_eval dc_nc_1628)

lemma dc_nc_1629: "dc_sub None 1629"
  by (dc_eval dc_nc_1629)

lemma dc_nc_1630: "dc_sub None 1630"
  by (dc_eval dc_nc_1630)

lemma dc_nc_1631: "dc_sub None 1631"
  by (dc_eval dc_nc_1631)

lemma upt_nc_101: "[1616..<1632] = [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]"
  by (simp add: upt_rec)

lemma sec_nc_101: "\<forall>j\<in>{16 * 101..<16 * 101 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 101..<16 * 101 + 16}"
  then have "j \<in> set [1616..<1632]" unfolding set_upt by simp
  then have "j \<in> set [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]" unfolding upt_nc_101 .
  then show "dc_sub None j" using dc_nc_1616 dc_nc_1617 dc_nc_1618 dc_nc_1619 dc_nc_1620 dc_nc_1621 dc_nc_1622 dc_nc_1623 dc_nc_1624 dc_nc_1625 dc_nc_1626 dc_nc_1627 dc_nc_1628 dc_nc_1629 dc_nc_1630 dc_nc_1631
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
