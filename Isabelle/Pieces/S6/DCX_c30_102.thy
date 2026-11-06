theory DCX_c30_102
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1632: "dc_sub dc_b30 1632"
  by (dc_eval dc_c30_1632)

lemma dc_c30_1633: "dc_sub dc_b30 1633"
  by (dc_eval dc_c30_1633)

lemma dc_c30_1634: "dc_sub dc_b30 1634"
  by (dc_eval dc_c30_1634)

lemma dc_c30_1635: "dc_sub dc_b30 1635"
  by (dc_eval dc_c30_1635)

lemma dc_c30_1636: "dc_sub dc_b30 1636"
  by (dc_eval dc_c30_1636)

lemma dc_c30_1637: "dc_sub dc_b30 1637"
  by (dc_eval dc_c30_1637)

lemma dc_c30_1638: "dc_sub dc_b30 1638"
  by (dc_eval dc_c30_1638)

lemma dc_c30_1639: "dc_sub dc_b30 1639"
  by (dc_eval dc_c30_1639)

lemma dc_c30_1640: "dc_sub dc_b30 1640"
  by (dc_eval dc_c30_1640)

lemma dc_c30_1641: "dc_sub dc_b30 1641"
  by (dc_eval dc_c30_1641)

lemma dc_c30_1642: "dc_sub dc_b30 1642"
  by (dc_eval dc_c30_1642)

lemma dc_c30_1643: "dc_sub dc_b30 1643"
  by (dc_eval dc_c30_1643)

lemma dc_c30_1644: "dc_sub dc_b30 1644"
  by (dc_eval dc_c30_1644)

lemma dc_c30_1645: "dc_sub dc_b30 1645"
  by (dc_eval dc_c30_1645)

lemma dc_c30_1646: "dc_sub dc_b30 1646"
  by (dc_eval dc_c30_1646)

lemma dc_c30_1647: "dc_sub dc_b30 1647"
  by (dc_eval dc_c30_1647)

lemma upt_c30_102: "[1632..<1648] = [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]"
  by (simp add: upt_rec)

lemma sec_c30_102: "\<forall>j\<in>{16 * 102..<16 * 102 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 102..<16 * 102 + 16}"
  then have "j \<in> set [1632..<1648]" unfolding set_upt by simp
  then have "j \<in> set [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]" unfolding upt_c30_102 .
  then show "dc_sub dc_b30 j" using dc_c30_1632 dc_c30_1633 dc_c30_1634 dc_c30_1635 dc_c30_1636 dc_c30_1637 dc_c30_1638 dc_c30_1639 dc_c30_1640 dc_c30_1641 dc_c30_1642 dc_c30_1643 dc_c30_1644 dc_c30_1645 dc_c30_1646 dc_c30_1647
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
