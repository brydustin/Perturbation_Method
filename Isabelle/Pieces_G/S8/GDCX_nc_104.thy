theory GDCX_nc_104
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1664: "gdc_sub None 1664"
  by (gdc_eval gdc_nc_1664)

lemma gdc_nc_1665: "gdc_sub None 1665"
  by (gdc_eval gdc_nc_1665)

lemma gdc_nc_1666: "gdc_sub None 1666"
  by (gdc_eval gdc_nc_1666)

lemma gdc_nc_1667: "gdc_sub None 1667"
  by (gdc_eval gdc_nc_1667)

lemma gdc_nc_1668: "gdc_sub None 1668"
  by (gdc_eval gdc_nc_1668)

lemma gdc_nc_1669: "gdc_sub None 1669"
  by (gdc_eval gdc_nc_1669)

lemma gdc_nc_1670: "gdc_sub None 1670"
  by (gdc_eval gdc_nc_1670)

lemma gdc_nc_1671: "gdc_sub None 1671"
  by (gdc_eval gdc_nc_1671)

lemma gdc_nc_1672: "gdc_sub None 1672"
  by (gdc_eval gdc_nc_1672)

lemma gdc_nc_1673: "gdc_sub None 1673"
  by (gdc_eval gdc_nc_1673)

lemma gdc_nc_1674: "gdc_sub None 1674"
  by (gdc_eval gdc_nc_1674)

lemma gdc_nc_1675: "gdc_sub None 1675"
  by (gdc_eval gdc_nc_1675)

lemma gdc_nc_1676: "gdc_sub None 1676"
  by (gdc_eval gdc_nc_1676)

lemma gdc_nc_1677: "gdc_sub None 1677"
  by (gdc_eval gdc_nc_1677)

lemma gdc_nc_1678: "gdc_sub None 1678"
  by (gdc_eval gdc_nc_1678)

lemma gdc_nc_1679: "gdc_sub None 1679"
  by (gdc_eval gdc_nc_1679)

lemma gupt_nc_104: "[1664..<1680] = [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]"
  by (simp add: upt_rec)

lemma gsec_nc_104: "\<forall>j\<in>{16 * 104..<16 * 104 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 104..<16 * 104 + 16}"
  then have "j \<in> set [1664..<1680]" unfolding set_upt by simp
  then have "j \<in> set [1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679]" unfolding gupt_nc_104 .
  then show "gdc_sub None j" using gdc_nc_1664 gdc_nc_1665 gdc_nc_1666 gdc_nc_1667 gdc_nc_1668 gdc_nc_1669 gdc_nc_1670 gdc_nc_1671 gdc_nc_1672 gdc_nc_1673 gdc_nc_1674 gdc_nc_1675 gdc_nc_1676 gdc_nc_1677 gdc_nc_1678 gdc_nc_1679
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
