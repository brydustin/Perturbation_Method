theory DCX_c30_104
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1664: "dc_sub dc_b30 1664"
  by (dc_eval dc_c30_1664)

lemma dc_c30_1665: "dc_sub dc_b30 1665"
  by (dc_eval dc_c30_1665)

lemma dc_c30_1666: "dc_sub dc_b30 1666"
  by (dc_eval dc_c30_1666)

lemma dc_c30_1667: "dc_sub dc_b30 1667"
  by (dc_eval dc_c30_1667)

lemma dc_c30_1668: "dc_sub dc_b30 1668"
  by (dc_eval dc_c30_1668)

lemma dc_c30_1669: "dc_sub dc_b30 1669"
  by (dc_eval dc_c30_1669)

lemma dc_c30_1670: "dc_sub dc_b30 1670"
  by (dc_eval dc_c30_1670)

lemma dc_c30_1671: "dc_sub dc_b30 1671"
  by (dc_eval dc_c30_1671)

lemma dc_c30_1672: "dc_sub dc_b30 1672"
  by (dc_eval dc_c30_1672)

lemma dc_c30_1673: "dc_sub dc_b30 1673"
  by (dc_eval dc_c30_1673)

lemma dc_c30_1674: "dc_sub dc_b30 1674"
  by (dc_eval dc_c30_1674)

lemma dc_c30_1675: "dc_sub dc_b30 1675"
  by (dc_eval dc_c30_1675)

lemma dc_c30_1676: "dc_sub dc_b30 1676"
  by (dc_eval dc_c30_1676)

lemma dc_c30_1677: "dc_sub dc_b30 1677"
  by (dc_eval dc_c30_1677)

lemma dc_c30_1678: "dc_sub dc_b30 1678"
  by (dc_eval dc_c30_1678)

lemma dc_c30_1679: "dc_sub dc_b30 1679"
  by (dc_eval dc_c30_1679)

lemma upt_c30_104: "[1664..<1680] = [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]"
  by (simp add: upt_rec)

lemma sec_c30_104: "\<forall>j\<in>{16 * 104..<16 * 104 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 104..<16 * 104 + 16}"
  then have "j \<in> set [1664..<1680]" unfolding set_upt by simp
  then have "j \<in> set [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]" unfolding upt_c30_104 .
  then show "dc_sub dc_b30 j" using dc_c30_1664 dc_c30_1665 dc_c30_1666 dc_c30_1667 dc_c30_1668 dc_c30_1669 dc_c30_1670 dc_c30_1671 dc_c30_1672 dc_c30_1673 dc_c30_1674 dc_c30_1675 dc_c30_1676 dc_c30_1677 dc_c30_1678 dc_c30_1679
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
