theory GOCX_nc_107
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1712: "goc_sub None 1712"
  by (goc_eval goc_nc_1712)

lemma goc_nc_1713: "goc_sub None 1713"
  by (goc_eval goc_nc_1713)

lemma goc_nc_1714: "goc_sub None 1714"
  by (goc_eval goc_nc_1714)

lemma goc_nc_1715: "goc_sub None 1715"
  by (goc_eval goc_nc_1715)

lemma goc_nc_1716: "goc_sub None 1716"
  by (goc_eval goc_nc_1716)

lemma goc_nc_1717: "goc_sub None 1717"
  by (goc_eval goc_nc_1717)

lemma goc_nc_1718: "goc_sub None 1718"
  by (goc_eval goc_nc_1718)

lemma goc_nc_1719: "goc_sub None 1719"
  by (goc_eval goc_nc_1719)

lemma goc_nc_1720: "goc_sub None 1720"
  by (goc_eval goc_nc_1720)

lemma goc_nc_1721: "goc_sub None 1721"
  by (goc_eval goc_nc_1721)

lemma goc_nc_1722: "goc_sub None 1722"
  by (goc_eval goc_nc_1722)

lemma goc_nc_1723: "goc_sub None 1723"
  by (goc_eval goc_nc_1723)

lemma goc_nc_1724: "goc_sub None 1724"
  by (goc_eval goc_nc_1724)

lemma goc_nc_1725: "goc_sub None 1725"
  by (goc_eval goc_nc_1725)

lemma goc_nc_1726: "goc_sub None 1726"
  by (goc_eval goc_nc_1726)

lemma goc_nc_1727: "goc_sub None 1727"
  by (goc_eval goc_nc_1727)

lemma gupt_nc_107: "[1712..<1728] = [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]"
  by (simp add: upt_rec)

lemma gsec_nc_107: "\<forall>j\<in>{16 * 107..<16 * 107 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 107..<16 * 107 + 16}"
  then have "j \<in> set [1712..<1728]" unfolding set_upt by simp
  then have "j \<in> set [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]" unfolding gupt_nc_107 .
  then show "goc_sub None j" using goc_nc_1712 goc_nc_1713 goc_nc_1714 goc_nc_1715 goc_nc_1716 goc_nc_1717 goc_nc_1718 goc_nc_1719 goc_nc_1720 goc_nc_1721 goc_nc_1722 goc_nc_1723 goc_nc_1724 goc_nc_1725 goc_nc_1726 goc_nc_1727
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
