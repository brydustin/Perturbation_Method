theory OCX_nc_162
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2592: "oc_sub None 2592"
  by (oc_eval oc_nc_2592)

lemma oc_nc_2593: "oc_sub None 2593"
  by (oc_eval oc_nc_2593)

lemma oc_nc_2594: "oc_sub None 2594"
  by (oc_eval oc_nc_2594)

lemma oc_nc_2595: "oc_sub None 2595"
  by (oc_eval oc_nc_2595)

lemma oc_nc_2596: "oc_sub None 2596"
  by (oc_eval oc_nc_2596)

lemma oc_nc_2597: "oc_sub None 2597"
  by (oc_eval oc_nc_2597)

lemma oc_nc_2598: "oc_sub None 2598"
  by (oc_eval oc_nc_2598)

lemma oc_nc_2599: "oc_sub None 2599"
  by (oc_eval oc_nc_2599)

lemma oc_nc_2600: "oc_sub None 2600"
  by (oc_eval oc_nc_2600)

lemma oc_nc_2601: "oc_sub None 2601"
  by (oc_eval oc_nc_2601)

lemma oc_nc_2602: "oc_sub None 2602"
  by (oc_eval oc_nc_2602)

lemma oc_nc_2603: "oc_sub None 2603"
  by (oc_eval oc_nc_2603)

lemma oc_nc_2604: "oc_sub None 2604"
  by (oc_eval oc_nc_2604)

lemma oc_nc_2605: "oc_sub None 2605"
  by (oc_eval oc_nc_2605)

lemma oc_nc_2606: "oc_sub None 2606"
  by (oc_eval oc_nc_2606)

lemma oc_nc_2607: "oc_sub None 2607"
  by (oc_eval oc_nc_2607)

lemma upt_nc_162: "[2592..<2608] = [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]"
  by (simp add: upt_rec)

lemma sec_nc_162: "\<forall>j\<in>{16 * 162..<16 * 162 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 162..<16 * 162 + 16}"
  then have "j \<in> set [2592..<2608]" unfolding set_upt by simp
  then have "j \<in> set [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]" unfolding upt_nc_162 .
  then show "oc_sub None j" using oc_nc_2592 oc_nc_2593 oc_nc_2594 oc_nc_2595 oc_nc_2596 oc_nc_2597 oc_nc_2598 oc_nc_2599 oc_nc_2600 oc_nc_2601 oc_nc_2602 oc_nc_2603 oc_nc_2604 oc_nc_2605 oc_nc_2606 oc_nc_2607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
