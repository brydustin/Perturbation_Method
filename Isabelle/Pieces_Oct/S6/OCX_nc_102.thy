theory OCX_nc_102
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1632: "oc_sub None 1632"
  by (oc_eval oc_nc_1632)

lemma oc_nc_1633: "oc_sub None 1633"
  by (oc_eval oc_nc_1633)

lemma oc_nc_1634: "oc_sub None 1634"
  by (oc_eval oc_nc_1634)

lemma oc_nc_1635: "oc_sub None 1635"
  by (oc_eval oc_nc_1635)

lemma oc_nc_1636: "oc_sub None 1636"
  by (oc_eval oc_nc_1636)

lemma oc_nc_1637: "oc_sub None 1637"
  by (oc_eval oc_nc_1637)

lemma oc_nc_1638: "oc_sub None 1638"
  by (oc_eval oc_nc_1638)

lemma oc_nc_1639: "oc_sub None 1639"
  by (oc_eval oc_nc_1639)

lemma oc_nc_1640: "oc_sub None 1640"
  by (oc_eval oc_nc_1640)

lemma oc_nc_1641: "oc_sub None 1641"
  by (oc_eval oc_nc_1641)

lemma oc_nc_1642: "oc_sub None 1642"
  by (oc_eval oc_nc_1642)

lemma oc_nc_1643: "oc_sub None 1643"
  by (oc_eval oc_nc_1643)

lemma oc_nc_1644: "oc_sub None 1644"
  by (oc_eval oc_nc_1644)

lemma oc_nc_1645: "oc_sub None 1645"
  by (oc_eval oc_nc_1645)

lemma oc_nc_1646: "oc_sub None 1646"
  by (oc_eval oc_nc_1646)

lemma oc_nc_1647: "oc_sub None 1647"
  by (oc_eval oc_nc_1647)

lemma upt_nc_102: "[1632..<1648] = [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]"
  by (simp add: upt_rec)

lemma sec_nc_102: "\<forall>j\<in>{16 * 102..<16 * 102 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 102..<16 * 102 + 16}"
  then have "j \<in> set [1632..<1648]" unfolding set_upt by simp
  then have "j \<in> set [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]" unfolding upt_nc_102 .
  then show "oc_sub None j" using oc_nc_1632 oc_nc_1633 oc_nc_1634 oc_nc_1635 oc_nc_1636 oc_nc_1637 oc_nc_1638 oc_nc_1639 oc_nc_1640 oc_nc_1641 oc_nc_1642 oc_nc_1643 oc_nc_1644 oc_nc_1645 oc_nc_1646 oc_nc_1647
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
