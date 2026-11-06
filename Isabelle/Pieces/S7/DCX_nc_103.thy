theory DCX_nc_103
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1648: "dc_sub None 1648"
  by (dc_eval dc_nc_1648)

lemma dc_nc_1649: "dc_sub None 1649"
  by (dc_eval dc_nc_1649)

lemma dc_nc_1650: "dc_sub None 1650"
  by (dc_eval dc_nc_1650)

lemma dc_nc_1651: "dc_sub None 1651"
  by (dc_eval dc_nc_1651)

lemma dc_nc_1652: "dc_sub None 1652"
  by (dc_eval dc_nc_1652)

lemma dc_nc_1653: "dc_sub None 1653"
  by (dc_eval dc_nc_1653)

lemma dc_nc_1654: "dc_sub None 1654"
  by (dc_eval dc_nc_1654)

lemma dc_nc_1655: "dc_sub None 1655"
  by (dc_eval dc_nc_1655)

lemma dc_nc_1656: "dc_sub None 1656"
  by (dc_eval dc_nc_1656)

lemma dc_nc_1657: "dc_sub None 1657"
  by (dc_eval dc_nc_1657)

lemma dc_nc_1658: "dc_sub None 1658"
  by (dc_eval dc_nc_1658)

lemma dc_nc_1659: "dc_sub None 1659"
  by (dc_eval dc_nc_1659)

lemma dc_nc_1660: "dc_sub None 1660"
  by (dc_eval dc_nc_1660)

lemma dc_nc_1661: "dc_sub None 1661"
  by (dc_eval dc_nc_1661)

lemma dc_nc_1662: "dc_sub None 1662"
  by (dc_eval dc_nc_1662)

lemma dc_nc_1663: "dc_sub None 1663"
  by (dc_eval dc_nc_1663)

lemma upt_nc_103: "[1648..<1664] = [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]"
  by (simp add: upt_rec)

lemma sec_nc_103: "\<forall>j\<in>{16 * 103..<16 * 103 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 103..<16 * 103 + 16}"
  then have "j \<in> set [1648..<1664]" unfolding set_upt by simp
  then have "j \<in> set [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]" unfolding upt_nc_103 .
  then show "dc_sub None j" using dc_nc_1648 dc_nc_1649 dc_nc_1650 dc_nc_1651 dc_nc_1652 dc_nc_1653 dc_nc_1654 dc_nc_1655 dc_nc_1656 dc_nc_1657 dc_nc_1658 dc_nc_1659 dc_nc_1660 dc_nc_1661 dc_nc_1662 dc_nc_1663
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
