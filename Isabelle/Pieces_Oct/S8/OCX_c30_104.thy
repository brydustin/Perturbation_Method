theory OCX_c30_104
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1664: "oc_sub oc_b30 1664"
  by (oc_eval oc_c30_1664)

lemma oc_c30_1665: "oc_sub oc_b30 1665"
  by (oc_eval oc_c30_1665)

lemma oc_c30_1666: "oc_sub oc_b30 1666"
  by (oc_eval oc_c30_1666)

lemma oc_c30_1667: "oc_sub oc_b30 1667"
  by (oc_eval oc_c30_1667)

lemma oc_c30_1668: "oc_sub oc_b30 1668"
  by (oc_eval oc_c30_1668)

lemma oc_c30_1669: "oc_sub oc_b30 1669"
  by (oc_eval oc_c30_1669)

lemma oc_c30_1670: "oc_sub oc_b30 1670"
  by (oc_eval oc_c30_1670)

lemma oc_c30_1671: "oc_sub oc_b30 1671"
  by (oc_eval oc_c30_1671)

lemma oc_c30_1672: "oc_sub oc_b30 1672"
  by (oc_eval oc_c30_1672)

lemma oc_c30_1673: "oc_sub oc_b30 1673"
  by (oc_eval oc_c30_1673)

lemma oc_c30_1674: "oc_sub oc_b30 1674"
  by (oc_eval oc_c30_1674)

lemma oc_c30_1675: "oc_sub oc_b30 1675"
  by (oc_eval oc_c30_1675)

lemma oc_c30_1676: "oc_sub oc_b30 1676"
  by (oc_eval oc_c30_1676)

lemma oc_c30_1677: "oc_sub oc_b30 1677"
  by (oc_eval oc_c30_1677)

lemma oc_c30_1678: "oc_sub oc_b30 1678"
  by (oc_eval oc_c30_1678)

lemma oc_c30_1679: "oc_sub oc_b30 1679"
  by (oc_eval oc_c30_1679)

lemma upt_c30_104: "[1664..<1680] = [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]"
  by (simp add: upt_rec)

lemma sec_c30_104: "\<forall>j\<in>{16 * 104..<16 * 104 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 104..<16 * 104 + 16}"
  then have "j \<in> set [1664..<1680]" unfolding set_upt by simp
  then have "j \<in> set [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]" unfolding upt_c30_104 .
  then show "oc_sub oc_b30 j" using oc_c30_1664 oc_c30_1665 oc_c30_1666 oc_c30_1667 oc_c30_1668 oc_c30_1669 oc_c30_1670 oc_c30_1671 oc_c30_1672 oc_c30_1673 oc_c30_1674 oc_c30_1675 oc_c30_1676 oc_c30_1677 oc_c30_1678 oc_c30_1679
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
