theory DCX_nc_106
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1696: "dc_sub None 1696"
  by (dc_eval dc_nc_1696)

lemma dc_nc_1697: "dc_sub None 1697"
  by (dc_eval dc_nc_1697)

lemma dc_nc_1698: "dc_sub None 1698"
  by (dc_eval dc_nc_1698)

lemma dc_nc_1699: "dc_sub None 1699"
  by (dc_eval dc_nc_1699)

lemma dc_nc_1700: "dc_sub None 1700"
  by (dc_eval dc_nc_1700)

lemma dc_nc_1701: "dc_sub None 1701"
  by (dc_eval dc_nc_1701)

lemma dc_nc_1702: "dc_sub None 1702"
  by (dc_eval dc_nc_1702)

lemma dc_nc_1703: "dc_sub None 1703"
  by (dc_eval dc_nc_1703)

lemma dc_nc_1704: "dc_sub None 1704"
  by (dc_eval dc_nc_1704)

lemma dc_nc_1705: "dc_sub None 1705"
  by (dc_eval dc_nc_1705)

lemma dc_nc_1706: "dc_sub None 1706"
  by (dc_eval dc_nc_1706)

lemma dc_nc_1707: "dc_sub None 1707"
  by (dc_eval dc_nc_1707)

lemma dc_nc_1708: "dc_sub None 1708"
  by (dc_eval dc_nc_1708)

lemma dc_nc_1709: "dc_sub None 1709"
  by (dc_eval dc_nc_1709)

lemma dc_nc_1710: "dc_sub None 1710"
  by (dc_eval dc_nc_1710)

lemma dc_nc_1711: "dc_sub None 1711"
  by (dc_eval dc_nc_1711)

lemma upt_nc_106: "[1696..<1712] = [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]"
  by (simp add: upt_rec)

lemma sec_nc_106: "\<forall>j\<in>{16 * 106..<16 * 106 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 106..<16 * 106 + 16}"
  then have "j \<in> set [1696..<1712]" unfolding set_upt by simp
  then have "j \<in> set [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]" unfolding upt_nc_106 .
  then show "dc_sub None j" using dc_nc_1696 dc_nc_1697 dc_nc_1698 dc_nc_1699 dc_nc_1700 dc_nc_1701 dc_nc_1702 dc_nc_1703 dc_nc_1704 dc_nc_1705 dc_nc_1706 dc_nc_1707 dc_nc_1708 dc_nc_1709 dc_nc_1710 dc_nc_1711
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
