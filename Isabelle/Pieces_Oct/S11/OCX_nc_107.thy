theory OCX_nc_107
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1712: "oc_sub None 1712"
  by (oc_eval oc_nc_1712)

lemma oc_nc_1713: "oc_sub None 1713"
  by (oc_eval oc_nc_1713)

lemma oc_nc_1714: "oc_sub None 1714"
  by (oc_eval oc_nc_1714)

lemma oc_nc_1715: "oc_sub None 1715"
  by (oc_eval oc_nc_1715)

lemma oc_nc_1716: "oc_sub None 1716"
  by (oc_eval oc_nc_1716)

lemma oc_nc_1717: "oc_sub None 1717"
  by (oc_eval oc_nc_1717)

lemma oc_nc_1718: "oc_sub None 1718"
  by (oc_eval oc_nc_1718)

lemma oc_nc_1719: "oc_sub None 1719"
  by (oc_eval oc_nc_1719)

lemma oc_nc_1720: "oc_sub None 1720"
  by (oc_eval oc_nc_1720)

lemma oc_nc_1721: "oc_sub None 1721"
  by (oc_eval oc_nc_1721)

lemma oc_nc_1722: "oc_sub None 1722"
  by (oc_eval oc_nc_1722)

lemma oc_nc_1723: "oc_sub None 1723"
  by (oc_eval oc_nc_1723)

lemma oc_nc_1724: "oc_sub None 1724"
  by (oc_eval oc_nc_1724)

lemma oc_nc_1725: "oc_sub None 1725"
  by (oc_eval oc_nc_1725)

lemma oc_nc_1726: "oc_sub None 1726"
  by (oc_eval oc_nc_1726)

lemma oc_nc_1727: "oc_sub None 1727"
  by (oc_eval oc_nc_1727)

lemma upt_nc_107: "[1712..<1728] = [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]"
  by (simp add: upt_rec)

lemma sec_nc_107: "\<forall>j\<in>{16 * 107..<16 * 107 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 107..<16 * 107 + 16}"
  then have "j \<in> set [1712..<1728]" unfolding set_upt by simp
  then have "j \<in> set [1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727]" unfolding upt_nc_107 .
  then show "oc_sub None j" using oc_nc_1712 oc_nc_1713 oc_nc_1714 oc_nc_1715 oc_nc_1716 oc_nc_1717 oc_nc_1718 oc_nc_1719 oc_nc_1720 oc_nc_1721 oc_nc_1722 oc_nc_1723 oc_nc_1724 oc_nc_1725 oc_nc_1726 oc_nc_1727
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
