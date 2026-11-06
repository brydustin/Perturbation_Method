theory GDCX_nc_102
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1632: "gdc_sub None 1632"
  by (gdc_eval gdc_nc_1632)

lemma gdc_nc_1633: "gdc_sub None 1633"
  by (gdc_eval gdc_nc_1633)

lemma gdc_nc_1634: "gdc_sub None 1634"
  by (gdc_eval gdc_nc_1634)

lemma gdc_nc_1635: "gdc_sub None 1635"
  by (gdc_eval gdc_nc_1635)

lemma gdc_nc_1636: "gdc_sub None 1636"
  by (gdc_eval gdc_nc_1636)

lemma gdc_nc_1637: "gdc_sub None 1637"
  by (gdc_eval gdc_nc_1637)

lemma gdc_nc_1638: "gdc_sub None 1638"
  by (gdc_eval gdc_nc_1638)

lemma gdc_nc_1639: "gdc_sub None 1639"
  by (gdc_eval gdc_nc_1639)

lemma gdc_nc_1640: "gdc_sub None 1640"
  by (gdc_eval gdc_nc_1640)

lemma gdc_nc_1641: "gdc_sub None 1641"
  by (gdc_eval gdc_nc_1641)

lemma gdc_nc_1642: "gdc_sub None 1642"
  by (gdc_eval gdc_nc_1642)

lemma gdc_nc_1643: "gdc_sub None 1643"
  by (gdc_eval gdc_nc_1643)

lemma gdc_nc_1644: "gdc_sub None 1644"
  by (gdc_eval gdc_nc_1644)

lemma gdc_nc_1645: "gdc_sub None 1645"
  by (gdc_eval gdc_nc_1645)

lemma gdc_nc_1646: "gdc_sub None 1646"
  by (gdc_eval gdc_nc_1646)

lemma gdc_nc_1647: "gdc_sub None 1647"
  by (gdc_eval gdc_nc_1647)

lemma gupt_nc_102: "[1632..<1648] = [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]"
  by (simp add: upt_rec)

lemma gsec_nc_102: "\<forall>j\<in>{16 * 102..<16 * 102 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 102..<16 * 102 + 16}"
  then have "j \<in> set [1632..<1648]" unfolding set_upt by simp
  then have "j \<in> set [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]" unfolding gupt_nc_102 .
  then show "gdc_sub None j" using gdc_nc_1632 gdc_nc_1633 gdc_nc_1634 gdc_nc_1635 gdc_nc_1636 gdc_nc_1637 gdc_nc_1638 gdc_nc_1639 gdc_nc_1640 gdc_nc_1641 gdc_nc_1642 gdc_nc_1643 gdc_nc_1644 gdc_nc_1645 gdc_nc_1646 gdc_nc_1647
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
