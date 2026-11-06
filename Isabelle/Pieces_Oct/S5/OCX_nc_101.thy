theory OCX_nc_101
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1616: "oc_sub None 1616"
  by (oc_eval oc_nc_1616)

lemma oc_nc_1617: "oc_sub None 1617"
  by (oc_eval oc_nc_1617)

lemma oc_nc_1618: "oc_sub None 1618"
  by (oc_eval oc_nc_1618)

lemma oc_nc_1619: "oc_sub None 1619"
  by (oc_eval oc_nc_1619)

lemma oc_nc_1620: "oc_sub None 1620"
  by (oc_eval oc_nc_1620)

lemma oc_nc_1621: "oc_sub None 1621"
  by (oc_eval oc_nc_1621)

lemma oc_nc_1622: "oc_sub None 1622"
  by (oc_eval oc_nc_1622)

lemma oc_nc_1623: "oc_sub None 1623"
  by (oc_eval oc_nc_1623)

lemma oc_nc_1624: "oc_sub None 1624"
  by (oc_eval oc_nc_1624)

lemma oc_nc_1625: "oc_sub None 1625"
  by (oc_eval oc_nc_1625)

lemma oc_nc_1626: "oc_sub None 1626"
  by (oc_eval oc_nc_1626)

lemma oc_nc_1627: "oc_sub None 1627"
  by (oc_eval oc_nc_1627)

lemma oc_nc_1628: "oc_sub None 1628"
  by (oc_eval oc_nc_1628)

lemma oc_nc_1629: "oc_sub None 1629"
  by (oc_eval oc_nc_1629)

lemma oc_nc_1630: "oc_sub None 1630"
  by (oc_eval oc_nc_1630)

lemma oc_nc_1631: "oc_sub None 1631"
  by (oc_eval oc_nc_1631)

lemma upt_nc_101: "[1616..<1632] = [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]"
  by (simp add: upt_rec)

lemma sec_nc_101: "\<forall>j\<in>{16 * 101..<16 * 101 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 101..<16 * 101 + 16}"
  then have "j \<in> set [1616..<1632]" unfolding set_upt by simp
  then have "j \<in> set [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]" unfolding upt_nc_101 .
  then show "oc_sub None j" using oc_nc_1616 oc_nc_1617 oc_nc_1618 oc_nc_1619 oc_nc_1620 oc_nc_1621 oc_nc_1622 oc_nc_1623 oc_nc_1624 oc_nc_1625 oc_nc_1626 oc_nc_1627 oc_nc_1628 oc_nc_1629 oc_nc_1630 oc_nc_1631
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
