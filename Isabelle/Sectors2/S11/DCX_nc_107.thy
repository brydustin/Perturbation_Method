theory DCX_nc_107
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1712: "dc_sub None 1712"
  by (dc_eval dc_nc_1712)

lemma dc_nc_1713: "dc_sub None 1713"
  by (dc_eval dc_nc_1713)

lemma dc_nc_1714: "dc_sub None 1714"
  by (dc_eval dc_nc_1714)

lemma dc_nc_1715: "dc_sub None 1715"
  by (dc_eval dc_nc_1715)

lemma dc_nc_1716: "dc_sub None 1716"
  by (dc_eval dc_nc_1716)

lemma dc_nc_1717: "dc_sub None 1717"
  by (dc_eval dc_nc_1717)

lemma dc_nc_1718: "dc_sub None 1718"
  by (dc_eval dc_nc_1718)

lemma dc_nc_1719: "dc_sub None 1719"
  by (dc_eval dc_nc_1719)

lemma dc_nc_1720: "dc_sub None 1720"
  by (dc_eval dc_nc_1720)

lemma dc_nc_1721: "dc_sub None 1721"
  by (dc_eval dc_nc_1721)

lemma dc_nc_1722: "dc_sub None 1722"
  by (dc_eval dc_nc_1722)

lemma dc_nc_1723: "dc_sub None 1723"
  by (dc_eval dc_nc_1723)

lemma dc_nc_1724: "dc_sub None 1724"
  by (dc_eval dc_nc_1724)

lemma dc_nc_1725: "dc_sub None 1725"
  by (dc_eval dc_nc_1725)

lemma dc_nc_1726: "dc_sub None 1726"
  by (dc_eval dc_nc_1726)

lemma dc_nc_1727: "dc_sub None 1727"
  by (dc_eval dc_nc_1727)

lemma upt_nc_107: "[1712..<1728] = [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]"
  by (simp add: upt_rec)

lemma sec_nc_107: "\<forall>j\<in>{16 * 107..<16 * 107 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 107..<16 * 107 + 16}"
  then have "j \<in> set [1712..<1728]" unfolding set_upt by simp
  then have "j \<in> set [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]" unfolding upt_nc_107 .
  then show "dc_sub None j" using dc_nc_1712 dc_nc_1713 dc_nc_1714 dc_nc_1715 dc_nc_1716 dc_nc_1717 dc_nc_1718 dc_nc_1719 dc_nc_1720 dc_nc_1721 dc_nc_1722 dc_nc_1723 dc_nc_1724 dc_nc_1725 dc_nc_1726 dc_nc_1727
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
