theory OCX_c30_101
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1616: "oc_sub oc_b30 1616"
  by (oc_eval oc_c30_1616)

lemma oc_c30_1617: "oc_sub oc_b30 1617"
  by (oc_eval oc_c30_1617)

lemma oc_c30_1618: "oc_sub oc_b30 1618"
  by (oc_eval oc_c30_1618)

lemma oc_c30_1619: "oc_sub oc_b30 1619"
  by (oc_eval oc_c30_1619)

lemma oc_c30_1620: "oc_sub oc_b30 1620"
  by (oc_eval oc_c30_1620)

lemma oc_c30_1621: "oc_sub oc_b30 1621"
  by (oc_eval oc_c30_1621)

lemma oc_c30_1622: "oc_sub oc_b30 1622"
  by (oc_eval oc_c30_1622)

lemma oc_c30_1623: "oc_sub oc_b30 1623"
  by (oc_eval oc_c30_1623)

lemma oc_c30_1624: "oc_sub oc_b30 1624"
  by (oc_eval oc_c30_1624)

lemma oc_c30_1625: "oc_sub oc_b30 1625"
  by (oc_eval oc_c30_1625)

lemma oc_c30_1626: "oc_sub oc_b30 1626"
  by (oc_eval oc_c30_1626)

lemma oc_c30_1627: "oc_sub oc_b30 1627"
  by (oc_eval oc_c30_1627)

lemma oc_c30_1628: "oc_sub oc_b30 1628"
  by (oc_eval oc_c30_1628)

lemma oc_c30_1629: "oc_sub oc_b30 1629"
  by (oc_eval oc_c30_1629)

lemma oc_c30_1630: "oc_sub oc_b30 1630"
  by (oc_eval oc_c30_1630)

lemma oc_c30_1631: "oc_sub oc_b30 1631"
  by (oc_eval oc_c30_1631)

lemma upt_c30_101: "[1616..<1632] = [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]"
  by (simp add: upt_rec)

lemma sec_c30_101: "\<forall>j\<in>{16 * 101..<16 * 101 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 101..<16 * 101 + 16}"
  then have "j \<in> set [1616..<1632]" unfolding set_upt by simp
  then have "j \<in> set [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]" unfolding upt_c30_101 .
  then show "oc_sub oc_b30 j" using oc_c30_1616 oc_c30_1617 oc_c30_1618 oc_c30_1619 oc_c30_1620 oc_c30_1621 oc_c30_1622 oc_c30_1623 oc_c30_1624 oc_c30_1625 oc_c30_1626 oc_c30_1627 oc_c30_1628 oc_c30_1629 oc_c30_1630 oc_c30_1631
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
