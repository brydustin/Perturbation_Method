theory OCX_c30_162
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2592: "oc_sub oc_b30 2592"
  by (oc_eval oc_c30_2592)

lemma oc_c30_2593: "oc_sub oc_b30 2593"
  by (oc_eval oc_c30_2593)

lemma oc_c30_2594: "oc_sub oc_b30 2594"
  by (oc_eval oc_c30_2594)

lemma oc_c30_2595: "oc_sub oc_b30 2595"
  by (oc_eval oc_c30_2595)

lemma oc_c30_2596: "oc_sub oc_b30 2596"
  by (oc_eval oc_c30_2596)

lemma oc_c30_2597: "oc_sub oc_b30 2597"
  by (oc_eval oc_c30_2597)

lemma oc_c30_2598: "oc_sub oc_b30 2598"
  by (oc_eval oc_c30_2598)

lemma oc_c30_2599: "oc_sub oc_b30 2599"
  by (oc_eval oc_c30_2599)

lemma oc_c30_2600: "oc_sub oc_b30 2600"
  by (oc_eval oc_c30_2600)

lemma oc_c30_2601: "oc_sub oc_b30 2601"
  by (oc_eval oc_c30_2601)

lemma oc_c30_2602: "oc_sub oc_b30 2602"
  by (oc_eval oc_c30_2602)

lemma oc_c30_2603: "oc_sub oc_b30 2603"
  by (oc_eval oc_c30_2603)

lemma oc_c30_2604: "oc_sub oc_b30 2604"
  by (oc_eval oc_c30_2604)

lemma oc_c30_2605: "oc_sub oc_b30 2605"
  by (oc_eval oc_c30_2605)

lemma oc_c30_2606: "oc_sub oc_b30 2606"
  by (oc_eval oc_c30_2606)

lemma oc_c30_2607: "oc_sub oc_b30 2607"
  by (oc_eval oc_c30_2607)

lemma upt_c30_162: "[2592..<2608] = [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]"
  by (simp add: upt_rec)

lemma sec_c30_162: "\<forall>j\<in>{16 * 162..<16 * 162 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 162..<16 * 162 + 16}"
  then have "j \<in> set [2592..<2608]" unfolding set_upt by simp
  then have "j \<in> set [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]" unfolding upt_c30_162 .
  then show "oc_sub oc_b30 j" using oc_c30_2592 oc_c30_2593 oc_c30_2594 oc_c30_2595 oc_c30_2596 oc_c30_2597 oc_c30_2598 oc_c30_2599 oc_c30_2600 oc_c30_2601 oc_c30_2602 oc_c30_2603 oc_c30_2604 oc_c30_2605 oc_c30_2606 oc_c30_2607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
