theory OCX_c30_106
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1696: "oc_sub oc_b30 1696"
  by (oc_eval oc_c30_1696)

lemma oc_c30_1697: "oc_sub oc_b30 1697"
  by (oc_eval oc_c30_1697)

lemma oc_c30_1698: "oc_sub oc_b30 1698"
  by (oc_eval oc_c30_1698)

lemma oc_c30_1699: "oc_sub oc_b30 1699"
  by (oc_eval oc_c30_1699)

lemma oc_c30_1700: "oc_sub oc_b30 1700"
  by (oc_eval oc_c30_1700)

lemma oc_c30_1701: "oc_sub oc_b30 1701"
  by (oc_eval oc_c30_1701)

lemma oc_c30_1702: "oc_sub oc_b30 1702"
  by (oc_eval oc_c30_1702)

lemma oc_c30_1703: "oc_sub oc_b30 1703"
  by (oc_eval oc_c30_1703)

lemma oc_c30_1704: "oc_sub oc_b30 1704"
  by (oc_eval oc_c30_1704)

lemma oc_c30_1705: "oc_sub oc_b30 1705"
  by (oc_eval oc_c30_1705)

lemma oc_c30_1706: "oc_sub oc_b30 1706"
  by (oc_eval oc_c30_1706)

lemma oc_c30_1707: "oc_sub oc_b30 1707"
  by (oc_eval oc_c30_1707)

lemma oc_c30_1708: "oc_sub oc_b30 1708"
  by (oc_eval oc_c30_1708)

lemma oc_c30_1709: "oc_sub oc_b30 1709"
  by (oc_eval oc_c30_1709)

lemma oc_c30_1710: "oc_sub oc_b30 1710"
  by (oc_eval oc_c30_1710)

lemma oc_c30_1711: "oc_sub oc_b30 1711"
  by (oc_eval oc_c30_1711)

lemma upt_c30_106: "[1696..<1712] = [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]"
  by (simp add: upt_rec)

lemma sec_c30_106: "\<forall>j\<in>{16 * 106..<16 * 106 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 106..<16 * 106 + 16}"
  then have "j \<in> set [1696..<1712]" unfolding set_upt by simp
  then have "j \<in> set [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]" unfolding upt_c30_106 .
  then show "oc_sub oc_b30 j" using oc_c30_1696 oc_c30_1697 oc_c30_1698 oc_c30_1699 oc_c30_1700 oc_c30_1701 oc_c30_1702 oc_c30_1703 oc_c30_1704 oc_c30_1705 oc_c30_1706 oc_c30_1707 oc_c30_1708 oc_c30_1709 oc_c30_1710 oc_c30_1711
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
