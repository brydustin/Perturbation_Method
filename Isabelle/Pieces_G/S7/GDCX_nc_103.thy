theory GDCX_nc_103
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1648: "gdc_sub None 1648"
  by (gdc_eval gdc_nc_1648)

lemma gdc_nc_1649: "gdc_sub None 1649"
  by (gdc_eval gdc_nc_1649)

lemma gdc_nc_1650: "gdc_sub None 1650"
  by (gdc_eval gdc_nc_1650)

lemma gdc_nc_1651: "gdc_sub None 1651"
  by (gdc_eval gdc_nc_1651)

lemma gdc_nc_1652: "gdc_sub None 1652"
  by (gdc_eval gdc_nc_1652)

lemma gdc_nc_1653: "gdc_sub None 1653"
  by (gdc_eval gdc_nc_1653)

lemma gdc_nc_1654: "gdc_sub None 1654"
  by (gdc_eval gdc_nc_1654)

lemma gdc_nc_1655: "gdc_sub None 1655"
  by (gdc_eval gdc_nc_1655)

lemma gdc_nc_1656: "gdc_sub None 1656"
  by (gdc_eval gdc_nc_1656)

lemma gdc_nc_1657: "gdc_sub None 1657"
  by (gdc_eval gdc_nc_1657)

lemma gdc_nc_1658: "gdc_sub None 1658"
  by (gdc_eval gdc_nc_1658)

lemma gdc_nc_1659: "gdc_sub None 1659"
  by (gdc_eval gdc_nc_1659)

lemma gdc_nc_1660: "gdc_sub None 1660"
  by (gdc_eval gdc_nc_1660)

lemma gdc_nc_1661: "gdc_sub None 1661"
  by (gdc_eval gdc_nc_1661)

lemma gdc_nc_1662: "gdc_sub None 1662"
  by (gdc_eval gdc_nc_1662)

lemma gdc_nc_1663: "gdc_sub None 1663"
  by (gdc_eval gdc_nc_1663)

lemma gupt_nc_103: "[1648..<1664] = [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]"
  by (simp add: upt_rec)

lemma gsec_nc_103: "\<forall>j\<in>{16 * 103..<16 * 103 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 103..<16 * 103 + 16}"
  then have "j \<in> set [1648..<1664]" unfolding set_upt by simp
  then have "j \<in> set [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]" unfolding gupt_nc_103 .
  then show "gdc_sub None j" using gdc_nc_1648 gdc_nc_1649 gdc_nc_1650 gdc_nc_1651 gdc_nc_1652 gdc_nc_1653 gdc_nc_1654 gdc_nc_1655 gdc_nc_1656 gdc_nc_1657 gdc_nc_1658 gdc_nc_1659 gdc_nc_1660 gdc_nc_1661 gdc_nc_1662 gdc_nc_1663
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
