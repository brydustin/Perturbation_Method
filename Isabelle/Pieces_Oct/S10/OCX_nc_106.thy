theory OCX_nc_106
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1696: "oc_sub None 1696"
  by (oc_eval oc_nc_1696)

lemma oc_nc_1697: "oc_sub None 1697"
  by (oc_eval oc_nc_1697)

lemma oc_nc_1698: "oc_sub None 1698"
  by (oc_eval oc_nc_1698)

lemma oc_nc_1699: "oc_sub None 1699"
  by (oc_eval oc_nc_1699)

lemma oc_nc_1700: "oc_sub None 1700"
  by (oc_eval oc_nc_1700)

lemma oc_nc_1701: "oc_sub None 1701"
  by (oc_eval oc_nc_1701)

lemma oc_nc_1702: "oc_sub None 1702"
  by (oc_eval oc_nc_1702)

lemma oc_nc_1703: "oc_sub None 1703"
  by (oc_eval oc_nc_1703)

lemma oc_nc_1704: "oc_sub None 1704"
  by (oc_eval oc_nc_1704)

lemma oc_nc_1705: "oc_sub None 1705"
  by (oc_eval oc_nc_1705)

lemma oc_nc_1706: "oc_sub None 1706"
  by (oc_eval oc_nc_1706)

lemma oc_nc_1707: "oc_sub None 1707"
  by (oc_eval oc_nc_1707)

lemma oc_nc_1708: "oc_sub None 1708"
  by (oc_eval oc_nc_1708)

lemma oc_nc_1709: "oc_sub None 1709"
  by (oc_eval oc_nc_1709)

lemma oc_nc_1710: "oc_sub None 1710"
  by (oc_eval oc_nc_1710)

lemma oc_nc_1711: "oc_sub None 1711"
  by (oc_eval oc_nc_1711)

lemma upt_nc_106: "[1696..<1712] = [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]"
  by (simp add: upt_rec)

lemma sec_nc_106: "\<forall>j\<in>{16 * 106..<16 * 106 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 106..<16 * 106 + 16}"
  then have "j \<in> set [1696..<1712]" unfolding set_upt by simp
  then have "j \<in> set [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]" unfolding upt_nc_106 .
  then show "oc_sub None j" using oc_nc_1696 oc_nc_1697 oc_nc_1698 oc_nc_1699 oc_nc_1700 oc_nc_1701 oc_nc_1702 oc_nc_1703 oc_nc_1704 oc_nc_1705 oc_nc_1706 oc_nc_1707 oc_nc_1708 oc_nc_1709 oc_nc_1710 oc_nc_1711
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
