theory DCX_c30_103
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1648: "dc_sub dc_b30 1648"
  by (dc_eval dc_c30_1648)

lemma dc_c30_1649: "dc_sub dc_b30 1649"
  by (dc_eval dc_c30_1649)

lemma dc_c30_1650: "dc_sub dc_b30 1650"
  by (dc_eval dc_c30_1650)

lemma dc_c30_1651: "dc_sub dc_b30 1651"
  by (dc_eval dc_c30_1651)

lemma dc_c30_1652: "dc_sub dc_b30 1652"
  by (dc_eval dc_c30_1652)

lemma dc_c30_1653: "dc_sub dc_b30 1653"
  by (dc_eval dc_c30_1653)

lemma dc_c30_1654: "dc_sub dc_b30 1654"
  by (dc_eval dc_c30_1654)

lemma dc_c30_1655: "dc_sub dc_b30 1655"
  by (dc_eval dc_c30_1655)

lemma dc_c30_1656: "dc_sub dc_b30 1656"
  by (dc_eval dc_c30_1656)

lemma dc_c30_1657: "dc_sub dc_b30 1657"
  by (dc_eval dc_c30_1657)

lemma dc_c30_1658: "dc_sub dc_b30 1658"
  by (dc_eval dc_c30_1658)

lemma dc_c30_1659: "dc_sub dc_b30 1659"
  by (dc_eval dc_c30_1659)

lemma dc_c30_1660: "dc_sub dc_b30 1660"
  by (dc_eval dc_c30_1660)

lemma dc_c30_1661: "dc_sub dc_b30 1661"
  by (dc_eval dc_c30_1661)

lemma dc_c30_1662: "dc_sub dc_b30 1662"
  by (dc_eval dc_c30_1662)

lemma dc_c30_1663: "dc_sub dc_b30 1663"
  by (dc_eval dc_c30_1663)

lemma upt_c30_103: "[1648..<1664] = [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]"
  by (simp add: upt_rec)

lemma sec_c30_103: "\<forall>j\<in>{16 * 103..<16 * 103 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 103..<16 * 103 + 16}"
  then have "j \<in> set [1648..<1664]" unfolding set_upt by simp
  then have "j \<in> set [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]" unfolding upt_c30_103 .
  then show "dc_sub dc_b30 j" using dc_c30_1648 dc_c30_1649 dc_c30_1650 dc_c30_1651 dc_c30_1652 dc_c30_1653 dc_c30_1654 dc_c30_1655 dc_c30_1656 dc_c30_1657 dc_c30_1658 dc_c30_1659 dc_c30_1660 dc_c30_1661 dc_c30_1662 dc_c30_1663
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
