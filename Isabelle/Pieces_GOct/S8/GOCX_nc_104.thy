theory GOCX_nc_104
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1664: "goc_sub None 1664"
  by (goc_eval goc_nc_1664)

lemma goc_nc_1665: "goc_sub None 1665"
  by (goc_eval goc_nc_1665)

lemma goc_nc_1666: "goc_sub None 1666"
  by (goc_eval goc_nc_1666)

lemma goc_nc_1667: "goc_sub None 1667"
  by (goc_eval goc_nc_1667)

lemma goc_nc_1668: "goc_sub None 1668"
  by (goc_eval goc_nc_1668)

lemma goc_nc_1669: "goc_sub None 1669"
  by (goc_eval goc_nc_1669)

lemma goc_nc_1670: "goc_sub None 1670"
  by (goc_eval goc_nc_1670)

lemma goc_nc_1671: "goc_sub None 1671"
  by (goc_eval goc_nc_1671)

lemma goc_nc_1672: "goc_sub None 1672"
  by (goc_eval goc_nc_1672)

lemma goc_nc_1673: "goc_sub None 1673"
  by (goc_eval goc_nc_1673)

lemma goc_nc_1674: "goc_sub None 1674"
  by (goc_eval goc_nc_1674)

lemma goc_nc_1675: "goc_sub None 1675"
  by (goc_eval goc_nc_1675)

lemma goc_nc_1676: "goc_sub None 1676"
  by (goc_eval goc_nc_1676)

lemma goc_nc_1677: "goc_sub None 1677"
  by (goc_eval goc_nc_1677)

lemma goc_nc_1678: "goc_sub None 1678"
  by (goc_eval goc_nc_1678)

lemma goc_nc_1679: "goc_sub None 1679"
  by (goc_eval goc_nc_1679)

lemma gupt_nc_104: "[1664..<1680] = [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]"
  by (simp add: upt_rec)

lemma gsec_nc_104: "\<forall>j\<in>{16 * 104..<16 * 104 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 104..<16 * 104 + 16}"
  then have "j \<in> set [1664..<1680]" unfolding set_upt by simp
  then have "j \<in> set [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]" unfolding gupt_nc_104 .
  then show "goc_sub None j" using goc_nc_1664 goc_nc_1665 goc_nc_1666 goc_nc_1667 goc_nc_1668 goc_nc_1669 goc_nc_1670 goc_nc_1671 goc_nc_1672 goc_nc_1673 goc_nc_1674 goc_nc_1675 goc_nc_1676 goc_nc_1677 goc_nc_1678 goc_nc_1679
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
