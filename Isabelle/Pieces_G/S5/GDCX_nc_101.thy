theory GDCX_nc_101
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1616: "gdc_sub None 1616"
  by (gdc_eval gdc_nc_1616)

lemma gdc_nc_1617: "gdc_sub None 1617"
  by (gdc_eval gdc_nc_1617)

lemma gdc_nc_1618: "gdc_sub None 1618"
  by (gdc_eval gdc_nc_1618)

lemma gdc_nc_1619: "gdc_sub None 1619"
  by (gdc_eval gdc_nc_1619)

lemma gdc_nc_1620: "gdc_sub None 1620"
  by (gdc_eval gdc_nc_1620)

lemma gdc_nc_1621: "gdc_sub None 1621"
  by (gdc_eval gdc_nc_1621)

lemma gdc_nc_1622: "gdc_sub None 1622"
  by (gdc_eval gdc_nc_1622)

lemma gdc_nc_1623: "gdc_sub None 1623"
  by (gdc_eval gdc_nc_1623)

lemma gdc_nc_1624: "gdc_sub None 1624"
  by (gdc_eval gdc_nc_1624)

lemma gdc_nc_1625: "gdc_sub None 1625"
  by (gdc_eval gdc_nc_1625)

lemma gdc_nc_1626: "gdc_sub None 1626"
  by (gdc_eval gdc_nc_1626)

lemma gdc_nc_1627: "gdc_sub None 1627"
  by (gdc_eval gdc_nc_1627)

lemma gdc_nc_1628: "gdc_sub None 1628"
  by (gdc_eval gdc_nc_1628)

lemma gdc_nc_1629: "gdc_sub None 1629"
  by (gdc_eval gdc_nc_1629)

lemma gdc_nc_1630: "gdc_sub None 1630"
  by (gdc_eval gdc_nc_1630)

lemma gdc_nc_1631: "gdc_sub None 1631"
  by (gdc_eval gdc_nc_1631)

lemma gupt_nc_101: "[1616..<1632] = [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]"
  by (simp add: upt_rec)

lemma gsec_nc_101: "\<forall>j\<in>{16 * 101..<16 * 101 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 101..<16 * 101 + 16}"
  then have "j \<in> set [1616..<1632]" unfolding set_upt by simp
  then have "j \<in> set [1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631]" unfolding gupt_nc_101 .
  then show "gdc_sub None j" using gdc_nc_1616 gdc_nc_1617 gdc_nc_1618 gdc_nc_1619 gdc_nc_1620 gdc_nc_1621 gdc_nc_1622 gdc_nc_1623 gdc_nc_1624 gdc_nc_1625 gdc_nc_1626 gdc_nc_1627 gdc_nc_1628 gdc_nc_1629 gdc_nc_1630 gdc_nc_1631
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
