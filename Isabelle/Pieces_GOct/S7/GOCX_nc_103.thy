theory GOCX_nc_103
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1648: "goc_sub None 1648"
  by (goc_eval goc_nc_1648)

lemma goc_nc_1649: "goc_sub None 1649"
  by (goc_eval goc_nc_1649)

lemma goc_nc_1650: "goc_sub None 1650"
  by (goc_eval goc_nc_1650)

lemma goc_nc_1651: "goc_sub None 1651"
  by (goc_eval goc_nc_1651)

lemma goc_nc_1652: "goc_sub None 1652"
  by (goc_eval goc_nc_1652)

lemma goc_nc_1653: "goc_sub None 1653"
  by (goc_eval goc_nc_1653)

lemma goc_nc_1654: "goc_sub None 1654"
  by (goc_eval goc_nc_1654)

lemma goc_nc_1655: "goc_sub None 1655"
  by (goc_eval goc_nc_1655)

lemma goc_nc_1656: "goc_sub None 1656"
  by (goc_eval goc_nc_1656)

lemma goc_nc_1657: "goc_sub None 1657"
  by (goc_eval goc_nc_1657)

lemma goc_nc_1658: "goc_sub None 1658"
  by (goc_eval goc_nc_1658)

lemma goc_nc_1659: "goc_sub None 1659"
  by (goc_eval goc_nc_1659)

lemma goc_nc_1660: "goc_sub None 1660"
  by (goc_eval goc_nc_1660)

lemma goc_nc_1661: "goc_sub None 1661"
  by (goc_eval goc_nc_1661)

lemma goc_nc_1662: "goc_sub None 1662"
  by (goc_eval goc_nc_1662)

lemma goc_nc_1663: "goc_sub None 1663"
  by (goc_eval goc_nc_1663)

lemma gupt_nc_103: "[1648..<1664] = [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]"
  by (simp add: upt_rec)

lemma gsec_nc_103: "\<forall>j\<in>{16 * 103..<16 * 103 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 103..<16 * 103 + 16}"
  then have "j \<in> set [1648..<1664]" unfolding set_upt by simp
  then have "j \<in> set [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]" unfolding gupt_nc_103 .
  then show "goc_sub None j" using goc_nc_1648 goc_nc_1649 goc_nc_1650 goc_nc_1651 goc_nc_1652 goc_nc_1653 goc_nc_1654 goc_nc_1655 goc_nc_1656 goc_nc_1657 goc_nc_1658 goc_nc_1659 goc_nc_1660 goc_nc_1661 goc_nc_1662 goc_nc_1663
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
