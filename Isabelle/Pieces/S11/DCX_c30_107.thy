theory DCX_c30_107
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1712: "dc_sub dc_b30 1712"
  by (dc_eval dc_c30_1712)

lemma dc_c30_1713: "dc_sub dc_b30 1713"
  by (dc_eval dc_c30_1713)

lemma dc_c30_1714: "dc_sub dc_b30 1714"
  by (dc_eval dc_c30_1714)

lemma dc_c30_1715: "dc_sub dc_b30 1715"
  by (dc_eval dc_c30_1715)

lemma dc_c30_1716: "dc_sub dc_b30 1716"
  by (dc_eval dc_c30_1716)

lemma dc_c30_1717: "dc_sub dc_b30 1717"
  by (dc_eval dc_c30_1717)

lemma dc_c30_1718: "dc_sub dc_b30 1718"
  by (dc_eval dc_c30_1718)

lemma dc_c30_1719: "dc_sub dc_b30 1719"
  by (dc_eval dc_c30_1719)

lemma dc_c30_1720: "dc_sub dc_b30 1720"
  by (dc_eval dc_c30_1720)

lemma dc_c30_1721: "dc_sub dc_b30 1721"
  by (dc_eval dc_c30_1721)

lemma dc_c30_1722: "dc_sub dc_b30 1722"
  by (dc_eval dc_c30_1722)

lemma dc_c30_1723: "dc_sub dc_b30 1723"
  by (dc_eval dc_c30_1723)

lemma dc_c30_1724: "dc_sub dc_b30 1724"
  by (dc_eval dc_c30_1724)

lemma dc_c30_1725: "dc_sub dc_b30 1725"
  by (dc_eval dc_c30_1725)

lemma dc_c30_1726: "dc_sub dc_b30 1726"
  by (dc_eval dc_c30_1726)

lemma dc_c30_1727: "dc_sub dc_b30 1727"
  by (dc_eval dc_c30_1727)

lemma upt_c30_107: "[1712..<1728] = [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]"
  by (simp add: upt_rec)

lemma sec_c30_107: "\<forall>j\<in>{16 * 107..<16 * 107 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 107..<16 * 107 + 16}"
  then have "j \<in> set [1712..<1728]" unfolding set_upt by simp
  then have "j \<in> set [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]" unfolding upt_c30_107 .
  then show "dc_sub dc_b30 j" using dc_c30_1712 dc_c30_1713 dc_c30_1714 dc_c30_1715 dc_c30_1716 dc_c30_1717 dc_c30_1718 dc_c30_1719 dc_c30_1720 dc_c30_1721 dc_c30_1722 dc_c30_1723 dc_c30_1724 dc_c30_1725 dc_c30_1726 dc_c30_1727
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
