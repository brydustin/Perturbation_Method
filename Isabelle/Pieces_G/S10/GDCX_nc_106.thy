theory GDCX_nc_106
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1696: "gdc_sub None 1696"
  by (gdc_eval gdc_nc_1696)

lemma gdc_nc_1697: "gdc_sub None 1697"
  by (gdc_eval gdc_nc_1697)

lemma gdc_nc_1698: "gdc_sub None 1698"
  by (gdc_eval gdc_nc_1698)

lemma gdc_nc_1699: "gdc_sub None 1699"
  by (gdc_eval gdc_nc_1699)

lemma gdc_nc_1700: "gdc_sub None 1700"
  by (gdc_eval gdc_nc_1700)

lemma gdc_nc_1701: "gdc_sub None 1701"
  by (gdc_eval gdc_nc_1701)

lemma gdc_nc_1702: "gdc_sub None 1702"
  by (gdc_eval gdc_nc_1702)

lemma gdc_nc_1703: "gdc_sub None 1703"
  by (gdc_eval gdc_nc_1703)

lemma gdc_nc_1704: "gdc_sub None 1704"
  by (gdc_eval gdc_nc_1704)

lemma gdc_nc_1705: "gdc_sub None 1705"
  by (gdc_eval gdc_nc_1705)

lemma gdc_nc_1706: "gdc_sub None 1706"
  by (gdc_eval gdc_nc_1706)

lemma gdc_nc_1707: "gdc_sub None 1707"
  by (gdc_eval gdc_nc_1707)

lemma gdc_nc_1708: "gdc_sub None 1708"
  by (gdc_eval gdc_nc_1708)

lemma gdc_nc_1709: "gdc_sub None 1709"
  by (gdc_eval gdc_nc_1709)

lemma gdc_nc_1710: "gdc_sub None 1710"
  by (gdc_eval gdc_nc_1710)

lemma gdc_nc_1711: "gdc_sub None 1711"
  by (gdc_eval gdc_nc_1711)

lemma gupt_nc_106: "[1696..<1712] = [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]"
  by (simp add: upt_rec)

lemma gsec_nc_106: "\<forall>j\<in>{16 * 106..<16 * 106 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 106..<16 * 106 + 16}"
  then have "j \<in> set [1696..<1712]" unfolding set_upt by simp
  then have "j \<in> set [1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711]" unfolding gupt_nc_106 .
  then show "gdc_sub None j" using gdc_nc_1696 gdc_nc_1697 gdc_nc_1698 gdc_nc_1699 gdc_nc_1700 gdc_nc_1701 gdc_nc_1702 gdc_nc_1703 gdc_nc_1704 gdc_nc_1705 gdc_nc_1706 gdc_nc_1707 gdc_nc_1708 gdc_nc_1709 gdc_nc_1710 gdc_nc_1711
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
