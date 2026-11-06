theory GOCX_nc_102
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1632: "goc_sub None 1632"
  by (goc_eval goc_nc_1632)

lemma goc_nc_1633: "goc_sub None 1633"
  by (goc_eval goc_nc_1633)

lemma goc_nc_1634: "goc_sub None 1634"
  by (goc_eval goc_nc_1634)

lemma goc_nc_1635: "goc_sub None 1635"
  by (goc_eval goc_nc_1635)

lemma goc_nc_1636: "goc_sub None 1636"
  by (goc_eval goc_nc_1636)

lemma goc_nc_1637: "goc_sub None 1637"
  by (goc_eval goc_nc_1637)

lemma goc_nc_1638: "goc_sub None 1638"
  by (goc_eval goc_nc_1638)

lemma goc_nc_1639: "goc_sub None 1639"
  by (goc_eval goc_nc_1639)

lemma goc_nc_1640: "goc_sub None 1640"
  by (goc_eval goc_nc_1640)

lemma goc_nc_1641: "goc_sub None 1641"
  by (goc_eval goc_nc_1641)

lemma goc_nc_1642: "goc_sub None 1642"
  by (goc_eval goc_nc_1642)

lemma goc_nc_1643: "goc_sub None 1643"
  by (goc_eval goc_nc_1643)

lemma goc_nc_1644: "goc_sub None 1644"
  by (goc_eval goc_nc_1644)

lemma goc_nc_1645: "goc_sub None 1645"
  by (goc_eval goc_nc_1645)

lemma goc_nc_1646: "goc_sub None 1646"
  by (goc_eval goc_nc_1646)

lemma goc_nc_1647: "goc_sub None 1647"
  by (goc_eval goc_nc_1647)

lemma gupt_nc_102: "[1632..<1648] = [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]"
  by (simp add: upt_rec)

lemma gsec_nc_102: "\<forall>j\<in>{16 * 102..<16 * 102 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 102..<16 * 102 + 16}"
  then have "j \<in> set [1632..<1648]" unfolding set_upt by simp
  then have "j \<in> set [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]" unfolding gupt_nc_102 .
  then show "goc_sub None j" using goc_nc_1632 goc_nc_1633 goc_nc_1634 goc_nc_1635 goc_nc_1636 goc_nc_1637 goc_nc_1638 goc_nc_1639 goc_nc_1640 goc_nc_1641 goc_nc_1642 goc_nc_1643 goc_nc_1644 goc_nc_1645 goc_nc_1646 goc_nc_1647
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
