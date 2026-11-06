theory OCX_nc_104
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1664: "oc_sub None 1664"
  by (oc_eval oc_nc_1664)

lemma oc_nc_1665: "oc_sub None 1665"
  by (oc_eval oc_nc_1665)

lemma oc_nc_1666: "oc_sub None 1666"
  by (oc_eval oc_nc_1666)

lemma oc_nc_1667: "oc_sub None 1667"
  by (oc_eval oc_nc_1667)

lemma oc_nc_1668: "oc_sub None 1668"
  by (oc_eval oc_nc_1668)

lemma oc_nc_1669: "oc_sub None 1669"
  by (oc_eval oc_nc_1669)

lemma oc_nc_1670: "oc_sub None 1670"
  by (oc_eval oc_nc_1670)

lemma oc_nc_1671: "oc_sub None 1671"
  by (oc_eval oc_nc_1671)

lemma oc_nc_1672: "oc_sub None 1672"
  by (oc_eval oc_nc_1672)

lemma oc_nc_1673: "oc_sub None 1673"
  by (oc_eval oc_nc_1673)

lemma oc_nc_1674: "oc_sub None 1674"
  by (oc_eval oc_nc_1674)

lemma oc_nc_1675: "oc_sub None 1675"
  by (oc_eval oc_nc_1675)

lemma oc_nc_1676: "oc_sub None 1676"
  by (oc_eval oc_nc_1676)

lemma oc_nc_1677: "oc_sub None 1677"
  by (oc_eval oc_nc_1677)

lemma oc_nc_1678: "oc_sub None 1678"
  by (oc_eval oc_nc_1678)

lemma oc_nc_1679: "oc_sub None 1679"
  by (oc_eval oc_nc_1679)

lemma upt_nc_104: "[1664..<1680] = [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]"
  by (simp add: upt_rec)

lemma sec_nc_104: "\<forall>j\<in>{16 * 104..<16 * 104 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 104..<16 * 104 + 16}"
  then have "j \<in> set [1664..<1680]" unfolding set_upt by simp
  then have "j \<in> set [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]" unfolding upt_nc_104 .
  then show "oc_sub None j" using oc_nc_1664 oc_nc_1665 oc_nc_1666 oc_nc_1667 oc_nc_1668 oc_nc_1669 oc_nc_1670 oc_nc_1671 oc_nc_1672 oc_nc_1673 oc_nc_1674 oc_nc_1675 oc_nc_1676 oc_nc_1677 oc_nc_1678 oc_nc_1679
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
