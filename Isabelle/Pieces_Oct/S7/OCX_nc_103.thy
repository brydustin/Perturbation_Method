theory OCX_nc_103
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1648: "oc_sub None 1648"
  by (oc_eval oc_nc_1648)

lemma oc_nc_1649: "oc_sub None 1649"
  by (oc_eval oc_nc_1649)

lemma oc_nc_1650: "oc_sub None 1650"
  by (oc_eval oc_nc_1650)

lemma oc_nc_1651: "oc_sub None 1651"
  by (oc_eval oc_nc_1651)

lemma oc_nc_1652: "oc_sub None 1652"
  by (oc_eval oc_nc_1652)

lemma oc_nc_1653: "oc_sub None 1653"
  by (oc_eval oc_nc_1653)

lemma oc_nc_1654: "oc_sub None 1654"
  by (oc_eval oc_nc_1654)

lemma oc_nc_1655: "oc_sub None 1655"
  by (oc_eval oc_nc_1655)

lemma oc_nc_1656: "oc_sub None 1656"
  by (oc_eval oc_nc_1656)

lemma oc_nc_1657: "oc_sub None 1657"
  by (oc_eval oc_nc_1657)

lemma oc_nc_1658: "oc_sub None 1658"
  by (oc_eval oc_nc_1658)

lemma oc_nc_1659: "oc_sub None 1659"
  by (oc_eval oc_nc_1659)

lemma oc_nc_1660: "oc_sub None 1660"
  by (oc_eval oc_nc_1660)

lemma oc_nc_1661: "oc_sub None 1661"
  by (oc_eval oc_nc_1661)

lemma oc_nc_1662: "oc_sub None 1662"
  by (oc_eval oc_nc_1662)

lemma oc_nc_1663: "oc_sub None 1663"
  by (oc_eval oc_nc_1663)

lemma upt_nc_103: "[1648..<1664] = [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]"
  by (simp add: upt_rec)

lemma sec_nc_103: "\<forall>j\<in>{16 * 103..<16 * 103 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 103..<16 * 103 + 16}"
  then have "j \<in> set [1648..<1664]" unfolding set_upt by simp
  then have "j \<in> set [1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663]" unfolding upt_nc_103 .
  then show "oc_sub None j" using oc_nc_1648 oc_nc_1649 oc_nc_1650 oc_nc_1651 oc_nc_1652 oc_nc_1653 oc_nc_1654 oc_nc_1655 oc_nc_1656 oc_nc_1657 oc_nc_1658 oc_nc_1659 oc_nc_1660 oc_nc_1661 oc_nc_1662 oc_nc_1663
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
