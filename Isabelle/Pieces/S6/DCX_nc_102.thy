theory DCX_nc_102
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1632: "dc_sub None 1632"
  by (dc_eval dc_nc_1632)

lemma dc_nc_1633: "dc_sub None 1633"
  by (dc_eval dc_nc_1633)

lemma dc_nc_1634: "dc_sub None 1634"
  by (dc_eval dc_nc_1634)

lemma dc_nc_1635: "dc_sub None 1635"
  by (dc_eval dc_nc_1635)

lemma dc_nc_1636: "dc_sub None 1636"
  by (dc_eval dc_nc_1636)

lemma dc_nc_1637: "dc_sub None 1637"
  by (dc_eval dc_nc_1637)

lemma dc_nc_1638: "dc_sub None 1638"
  by (dc_eval dc_nc_1638)

lemma dc_nc_1639: "dc_sub None 1639"
  by (dc_eval dc_nc_1639)

lemma dc_nc_1640: "dc_sub None 1640"
  by (dc_eval dc_nc_1640)

lemma dc_nc_1641: "dc_sub None 1641"
  by (dc_eval dc_nc_1641)

lemma dc_nc_1642: "dc_sub None 1642"
  by (dc_eval dc_nc_1642)

lemma dc_nc_1643: "dc_sub None 1643"
  by (dc_eval dc_nc_1643)

lemma dc_nc_1644: "dc_sub None 1644"
  by (dc_eval dc_nc_1644)

lemma dc_nc_1645: "dc_sub None 1645"
  by (dc_eval dc_nc_1645)

lemma dc_nc_1646: "dc_sub None 1646"
  by (dc_eval dc_nc_1646)

lemma dc_nc_1647: "dc_sub None 1647"
  by (dc_eval dc_nc_1647)

lemma upt_nc_102: "[1632..<1648] = [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]"
  by (simp add: upt_rec)

lemma sec_nc_102: "\<forall>j\<in>{16 * 102..<16 * 102 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 102..<16 * 102 + 16}"
  then have "j \<in> set [1632..<1648]" unfolding set_upt by simp
  then have "j \<in> set [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]" unfolding upt_nc_102 .
  then show "dc_sub None j" using dc_nc_1632 dc_nc_1633 dc_nc_1634 dc_nc_1635 dc_nc_1636 dc_nc_1637 dc_nc_1638 dc_nc_1639 dc_nc_1640 dc_nc_1641 dc_nc_1642 dc_nc_1643 dc_nc_1644 dc_nc_1645 dc_nc_1646 dc_nc_1647
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
