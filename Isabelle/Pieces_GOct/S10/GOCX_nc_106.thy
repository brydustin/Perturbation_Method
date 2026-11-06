theory GOCX_nc_106
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1696: "goc_sub None 1696"
  by (goc_eval goc_nc_1696)

lemma goc_nc_1697: "goc_sub None 1697"
  by (goc_eval goc_nc_1697)

lemma goc_nc_1698: "goc_sub None 1698"
  by (goc_eval goc_nc_1698)

lemma goc_nc_1699: "goc_sub None 1699"
  by (goc_eval goc_nc_1699)

lemma goc_nc_1700: "goc_sub None 1700"
  by (goc_eval goc_nc_1700)

lemma goc_nc_1701: "goc_sub None 1701"
  by (goc_eval goc_nc_1701)

lemma goc_nc_1702: "goc_sub None 1702"
  by (goc_eval goc_nc_1702)

lemma goc_nc_1703: "goc_sub None 1703"
  by (goc_eval goc_nc_1703)

lemma goc_nc_1704: "goc_sub None 1704"
  by (goc_eval goc_nc_1704)

lemma goc_nc_1705: "goc_sub None 1705"
  by (goc_eval goc_nc_1705)

lemma goc_nc_1706: "goc_sub None 1706"
  by (goc_eval goc_nc_1706)

lemma goc_nc_1707: "goc_sub None 1707"
  by (goc_eval goc_nc_1707)

lemma goc_nc_1708: "goc_sub None 1708"
  by (goc_eval goc_nc_1708)

lemma goc_nc_1709: "goc_sub None 1709"
  by (goc_eval goc_nc_1709)

lemma goc_nc_1710: "goc_sub None 1710"
  by (goc_eval goc_nc_1710)

lemma goc_nc_1711: "goc_sub None 1711"
  by (goc_eval goc_nc_1711)

lemma gupt_nc_106: "[1696..<1712] = [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]"
  by (simp add: upt_rec)

lemma gsec_nc_106: "\<forall>j\<in>{16 * 106..<16 * 106 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 106..<16 * 106 + 16}"
  then have "j \<in> set [1696..<1712]" unfolding set_upt by simp
  then have "j \<in> set [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]" unfolding gupt_nc_106 .
  then show "goc_sub None j" using goc_nc_1696 goc_nc_1697 goc_nc_1698 goc_nc_1699 goc_nc_1700 goc_nc_1701 goc_nc_1702 goc_nc_1703 goc_nc_1704 goc_nc_1705 goc_nc_1706 goc_nc_1707 goc_nc_1708 goc_nc_1709 goc_nc_1710 goc_nc_1711
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
