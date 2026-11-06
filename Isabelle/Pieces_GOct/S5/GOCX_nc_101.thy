theory GOCX_nc_101
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1616: "goc_sub None 1616"
  by (goc_eval goc_nc_1616)

lemma goc_nc_1617: "goc_sub None 1617"
  by (goc_eval goc_nc_1617)

lemma goc_nc_1618: "goc_sub None 1618"
  by (goc_eval goc_nc_1618)

lemma goc_nc_1619: "goc_sub None 1619"
  by (goc_eval goc_nc_1619)

lemma goc_nc_1620: "goc_sub None 1620"
  by (goc_eval goc_nc_1620)

lemma goc_nc_1621: "goc_sub None 1621"
  by (goc_eval goc_nc_1621)

lemma goc_nc_1622: "goc_sub None 1622"
  by (goc_eval goc_nc_1622)

lemma goc_nc_1623: "goc_sub None 1623"
  by (goc_eval goc_nc_1623)

lemma goc_nc_1624: "goc_sub None 1624"
  by (goc_eval goc_nc_1624)

lemma goc_nc_1625: "goc_sub None 1625"
  by (goc_eval goc_nc_1625)

lemma goc_nc_1626: "goc_sub None 1626"
  by (goc_eval goc_nc_1626)

lemma goc_nc_1627: "goc_sub None 1627"
  by (goc_eval goc_nc_1627)

lemma goc_nc_1628: "goc_sub None 1628"
  by (goc_eval goc_nc_1628)

lemma goc_nc_1629: "goc_sub None 1629"
  by (goc_eval goc_nc_1629)

lemma goc_nc_1630: "goc_sub None 1630"
  by (goc_eval goc_nc_1630)

lemma goc_nc_1631: "goc_sub None 1631"
  by (goc_eval goc_nc_1631)

lemma gupt_nc_101: "[1616..<1632] = [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]"
  by (simp add: upt_rec)

lemma gsec_nc_101: "\<forall>j\<in>{16 * 101..<16 * 101 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 101..<16 * 101 + 16}"
  then have "j \<in> set [1616..<1632]" unfolding set_upt by simp
  then have "j \<in> set [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]" unfolding gupt_nc_101 .
  then show "goc_sub None j" using goc_nc_1616 goc_nc_1617 goc_nc_1618 goc_nc_1619 goc_nc_1620 goc_nc_1621 goc_nc_1622 goc_nc_1623 goc_nc_1624 goc_nc_1625 goc_nc_1626 goc_nc_1627 goc_nc_1628 goc_nc_1629 goc_nc_1630 goc_nc_1631
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
