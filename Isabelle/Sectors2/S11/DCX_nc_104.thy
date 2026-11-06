theory DCX_nc_104
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1664: "dc_sub None 1664"
  by (dc_eval dc_nc_1664)

lemma dc_nc_1665: "dc_sub None 1665"
  by (dc_eval dc_nc_1665)

lemma dc_nc_1666: "dc_sub None 1666"
  by (dc_eval dc_nc_1666)

lemma dc_nc_1667: "dc_sub None 1667"
  by (dc_eval dc_nc_1667)

lemma dc_nc_1668: "dc_sub None 1668"
  by (dc_eval dc_nc_1668)

lemma dc_nc_1669: "dc_sub None 1669"
  by (dc_eval dc_nc_1669)

lemma dc_nc_1670: "dc_sub None 1670"
  by (dc_eval dc_nc_1670)

lemma dc_nc_1671: "dc_sub None 1671"
  by (dc_eval dc_nc_1671)

lemma dc_nc_1672: "dc_sub None 1672"
  by (dc_eval dc_nc_1672)

lemma dc_nc_1673: "dc_sub None 1673"
  by (dc_eval dc_nc_1673)

lemma dc_nc_1674: "dc_sub None 1674"
  by (dc_eval dc_nc_1674)

lemma dc_nc_1675: "dc_sub None 1675"
  by (dc_eval dc_nc_1675)

lemma dc_nc_1676: "dc_sub None 1676"
  by (dc_eval dc_nc_1676)

lemma dc_nc_1677: "dc_sub None 1677"
  by (dc_eval dc_nc_1677)

lemma dc_nc_1678: "dc_sub None 1678"
  by (dc_eval dc_nc_1678)

lemma dc_nc_1679: "dc_sub None 1679"
  by (dc_eval dc_nc_1679)

lemma upt_nc_104: "[1664..<1680] = [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]"
  by (simp add: upt_rec)

lemma sec_nc_104: "\<forall>j\<in>{16 * 104..<16 * 104 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 104..<16 * 104 + 16}"
  then have "j \<in> set [1664..<1680]" unfolding set_upt by simp
  then have "j \<in> set [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]" unfolding upt_nc_104 .
  then show "dc_sub None j" using dc_nc_1664 dc_nc_1665 dc_nc_1666 dc_nc_1667 dc_nc_1668 dc_nc_1669 dc_nc_1670 dc_nc_1671 dc_nc_1672 dc_nc_1673 dc_nc_1674 dc_nc_1675 dc_nc_1676 dc_nc_1677 dc_nc_1678 dc_nc_1679
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
