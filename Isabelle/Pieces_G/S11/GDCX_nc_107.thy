theory GDCX_nc_107
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1712: "gdc_sub None 1712"
  by (gdc_eval gdc_nc_1712)

lemma gdc_nc_1713: "gdc_sub None 1713"
  by (gdc_eval gdc_nc_1713)

lemma gdc_nc_1714: "gdc_sub None 1714"
  by (gdc_eval gdc_nc_1714)

lemma gdc_nc_1715: "gdc_sub None 1715"
  by (gdc_eval gdc_nc_1715)

lemma gdc_nc_1716: "gdc_sub None 1716"
  by (gdc_eval gdc_nc_1716)

lemma gdc_nc_1717: "gdc_sub None 1717"
  by (gdc_eval gdc_nc_1717)

lemma gdc_nc_1718: "gdc_sub None 1718"
  by (gdc_eval gdc_nc_1718)

lemma gdc_nc_1719: "gdc_sub None 1719"
  by (gdc_eval gdc_nc_1719)

lemma gdc_nc_1720: "gdc_sub None 1720"
  by (gdc_eval gdc_nc_1720)

lemma gdc_nc_1721: "gdc_sub None 1721"
  by (gdc_eval gdc_nc_1721)

lemma gdc_nc_1722: "gdc_sub None 1722"
  by (gdc_eval gdc_nc_1722)

lemma gdc_nc_1723: "gdc_sub None 1723"
  by (gdc_eval gdc_nc_1723)

lemma gdc_nc_1724: "gdc_sub None 1724"
  by (gdc_eval gdc_nc_1724)

lemma gdc_nc_1725: "gdc_sub None 1725"
  by (gdc_eval gdc_nc_1725)

lemma gdc_nc_1726: "gdc_sub None 1726"
  by (gdc_eval gdc_nc_1726)

lemma gdc_nc_1727: "gdc_sub None 1727"
  by (gdc_eval gdc_nc_1727)

lemma gupt_nc_107: "[1712..<1728] = [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]"
  by (simp add: upt_rec)

lemma gsec_nc_107: "\<forall>j\<in>{16 * 107..<16 * 107 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 107..<16 * 107 + 16}"
  then have "j \<in> set [1712..<1728]" unfolding set_upt by simp
  then have "j \<in> set [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]" unfolding gupt_nc_107 .
  then show "gdc_sub None j" using gdc_nc_1712 gdc_nc_1713 gdc_nc_1714 gdc_nc_1715 gdc_nc_1716 gdc_nc_1717 gdc_nc_1718 gdc_nc_1719 gdc_nc_1720 gdc_nc_1721 gdc_nc_1722 gdc_nc_1723 gdc_nc_1724 gdc_nc_1725 gdc_nc_1726 gdc_nc_1727
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
