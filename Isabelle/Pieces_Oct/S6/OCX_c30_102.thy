theory OCX_c30_102
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1632: "oc_sub oc_b30 1632"
  by (oc_eval oc_c30_1632)

lemma oc_c30_1633: "oc_sub oc_b30 1633"
  by (oc_eval oc_c30_1633)

lemma oc_c30_1634: "oc_sub oc_b30 1634"
  by (oc_eval oc_c30_1634)

lemma oc_c30_1635: "oc_sub oc_b30 1635"
  by (oc_eval oc_c30_1635)

lemma oc_c30_1636: "oc_sub oc_b30 1636"
  by (oc_eval oc_c30_1636)

lemma oc_c30_1637: "oc_sub oc_b30 1637"
  by (oc_eval oc_c30_1637)

lemma oc_c30_1638: "oc_sub oc_b30 1638"
  by (oc_eval oc_c30_1638)

lemma oc_c30_1639: "oc_sub oc_b30 1639"
  by (oc_eval oc_c30_1639)

lemma oc_c30_1640: "oc_sub oc_b30 1640"
  by (oc_eval oc_c30_1640)

lemma oc_c30_1641: "oc_sub oc_b30 1641"
  by (oc_eval oc_c30_1641)

lemma oc_c30_1642: "oc_sub oc_b30 1642"
  by (oc_eval oc_c30_1642)

lemma oc_c30_1643: "oc_sub oc_b30 1643"
  by (oc_eval oc_c30_1643)

lemma oc_c30_1644: "oc_sub oc_b30 1644"
  by (oc_eval oc_c30_1644)

lemma oc_c30_1645: "oc_sub oc_b30 1645"
  by (oc_eval oc_c30_1645)

lemma oc_c30_1646: "oc_sub oc_b30 1646"
  by (oc_eval oc_c30_1646)

lemma oc_c30_1647: "oc_sub oc_b30 1647"
  by (oc_eval oc_c30_1647)

lemma upt_c30_102: "[1632..<1648] = [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]"
  by (simp add: upt_rec)

lemma sec_c30_102: "\<forall>j\<in>{16 * 102..<16 * 102 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 102..<16 * 102 + 16}"
  then have "j \<in> set [1632..<1648]" unfolding set_upt by simp
  then have "j \<in> set [1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647]" unfolding upt_c30_102 .
  then show "oc_sub oc_b30 j" using oc_c30_1632 oc_c30_1633 oc_c30_1634 oc_c30_1635 oc_c30_1636 oc_c30_1637 oc_c30_1638 oc_c30_1639 oc_c30_1640 oc_c30_1641 oc_c30_1642 oc_c30_1643 oc_c30_1644 oc_c30_1645 oc_c30_1646 oc_c30_1647
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
