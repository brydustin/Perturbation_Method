theory DCX_c30_106
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1696: "dc_sub dc_b30 1696"
  by (dc_eval dc_c30_1696)

lemma dc_c30_1697: "dc_sub dc_b30 1697"
  by (dc_eval dc_c30_1697)

lemma dc_c30_1698: "dc_sub dc_b30 1698"
  by (dc_eval dc_c30_1698)

lemma dc_c30_1699: "dc_sub dc_b30 1699"
  by (dc_eval dc_c30_1699)

lemma dc_c30_1700: "dc_sub dc_b30 1700"
  by (dc_eval dc_c30_1700)

lemma dc_c30_1701: "dc_sub dc_b30 1701"
  by (dc_eval dc_c30_1701)

lemma dc_c30_1702: "dc_sub dc_b30 1702"
  by (dc_eval dc_c30_1702)

lemma dc_c30_1703: "dc_sub dc_b30 1703"
  by (dc_eval dc_c30_1703)

lemma dc_c30_1704: "dc_sub dc_b30 1704"
  by (dc_eval dc_c30_1704)

lemma dc_c30_1705: "dc_sub dc_b30 1705"
  by (dc_eval dc_c30_1705)

lemma dc_c30_1706: "dc_sub dc_b30 1706"
  by (dc_eval dc_c30_1706)

lemma dc_c30_1707: "dc_sub dc_b30 1707"
  by (dc_eval dc_c30_1707)

lemma dc_c30_1708: "dc_sub dc_b30 1708"
  by (dc_eval dc_c30_1708)

lemma dc_c30_1709: "dc_sub dc_b30 1709"
  by (dc_eval dc_c30_1709)

lemma dc_c30_1710: "dc_sub dc_b30 1710"
  by (dc_eval dc_c30_1710)

lemma dc_c30_1711: "dc_sub dc_b30 1711"
  by (dc_eval dc_c30_1711)

lemma upt_c30_106: "[1696..<1712] = [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]"
  by (simp add: upt_rec)

lemma sec_c30_106: "\<forall>j\<in>{16 * 106..<16 * 106 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 106..<16 * 106 + 16}"
  then have "j \<in> set [1696..<1712]" unfolding set_upt by simp
  then have "j \<in> set [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]" unfolding upt_c30_106 .
  then show "dc_sub dc_b30 j" using dc_c30_1696 dc_c30_1697 dc_c30_1698 dc_c30_1699 dc_c30_1700 dc_c30_1701 dc_c30_1702 dc_c30_1703 dc_c30_1704 dc_c30_1705 dc_c30_1706 dc_c30_1707 dc_c30_1708 dc_c30_1709 dc_c30_1710 dc_c30_1711
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
