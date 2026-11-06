theory DCX_c30_162
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2592: "dc_sub dc_b30 2592"
  by (dc_eval dc_c30_2592)

lemma dc_c30_2593: "dc_sub dc_b30 2593"
  by (dc_eval dc_c30_2593)

lemma dc_c30_2594: "dc_sub dc_b30 2594"
  by (dc_eval dc_c30_2594)

lemma dc_c30_2595: "dc_sub dc_b30 2595"
  by (dc_eval dc_c30_2595)

lemma dc_c30_2596: "dc_sub dc_b30 2596"
  by (dc_eval dc_c30_2596)

lemma dc_c30_2597: "dc_sub dc_b30 2597"
  by (dc_eval dc_c30_2597)

lemma dc_c30_2598: "dc_sub dc_b30 2598"
  by (dc_eval dc_c30_2598)

lemma dc_c30_2599: "dc_sub dc_b30 2599"
  by (dc_eval dc_c30_2599)

lemma dc_c30_2600: "dc_sub dc_b30 2600"
  by (dc_eval dc_c30_2600)

lemma dc_c30_2601: "dc_sub dc_b30 2601"
  by (dc_eval dc_c30_2601)

lemma dc_c30_2602: "dc_sub dc_b30 2602"
  by (dc_eval dc_c30_2602)

lemma dc_c30_2603: "dc_sub dc_b30 2603"
  by (dc_eval dc_c30_2603)

lemma dc_c30_2604: "dc_sub dc_b30 2604"
  by (dc_eval dc_c30_2604)

lemma dc_c30_2605: "dc_sub dc_b30 2605"
  by (dc_eval dc_c30_2605)

lemma dc_c30_2606: "dc_sub dc_b30 2606"
  by (dc_eval dc_c30_2606)

lemma dc_c30_2607: "dc_sub dc_b30 2607"
  by (dc_eval dc_c30_2607)

lemma upt_c30_162: "[2592..<2608] = [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]"
  by (simp add: upt_rec)

lemma sec_c30_162: "\<forall>j\<in>{16 * 162..<16 * 162 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 162..<16 * 162 + 16}"
  then have "j \<in> set [2592..<2608]" unfolding set_upt by simp
  then have "j \<in> set [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]" unfolding upt_c30_162 .
  then show "dc_sub dc_b30 j" using dc_c30_2592 dc_c30_2593 dc_c30_2594 dc_c30_2595 dc_c30_2596 dc_c30_2597 dc_c30_2598 dc_c30_2599 dc_c30_2600 dc_c30_2601 dc_c30_2602 dc_c30_2603 dc_c30_2604 dc_c30_2605 dc_c30_2606 dc_c30_2607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
