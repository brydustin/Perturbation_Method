theory DCX_nc_162
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2592: "dc_sub None 2592"
  by (dc_eval dc_nc_2592)

lemma dc_nc_2593: "dc_sub None 2593"
  by (dc_eval dc_nc_2593)

lemma dc_nc_2594: "dc_sub None 2594"
  by (dc_eval dc_nc_2594)

lemma dc_nc_2595: "dc_sub None 2595"
  by (dc_eval dc_nc_2595)

lemma dc_nc_2596: "dc_sub None 2596"
  by (dc_eval dc_nc_2596)

lemma dc_nc_2597: "dc_sub None 2597"
  by (dc_eval dc_nc_2597)

lemma dc_nc_2598: "dc_sub None 2598"
  by (dc_eval dc_nc_2598)

lemma dc_nc_2599: "dc_sub None 2599"
  by (dc_eval dc_nc_2599)

lemma dc_nc_2600: "dc_sub None 2600"
  by (dc_eval dc_nc_2600)

lemma dc_nc_2601: "dc_sub None 2601"
  by (dc_eval dc_nc_2601)

lemma dc_nc_2602: "dc_sub None 2602"
  by (dc_eval dc_nc_2602)

lemma dc_nc_2603: "dc_sub None 2603"
  by (dc_eval dc_nc_2603)

lemma dc_nc_2604: "dc_sub None 2604"
  by (dc_eval dc_nc_2604)

lemma dc_nc_2605: "dc_sub None 2605"
  by (dc_eval dc_nc_2605)

lemma dc_nc_2606: "dc_sub None 2606"
  by (dc_eval dc_nc_2606)

lemma dc_nc_2607: "dc_sub None 2607"
  by (dc_eval dc_nc_2607)

lemma upt_nc_162: "[2592..<2608] = [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]"
  by (simp add: upt_rec)

lemma sec_nc_162: "\<forall>j\<in>{16 * 162..<16 * 162 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 162..<16 * 162 + 16}"
  then have "j \<in> set [2592..<2608]" unfolding set_upt by simp
  then have "j \<in> set [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]" unfolding upt_nc_162 .
  then show "dc_sub None j" using dc_nc_2592 dc_nc_2593 dc_nc_2594 dc_nc_2595 dc_nc_2596 dc_nc_2597 dc_nc_2598 dc_nc_2599 dc_nc_2600 dc_nc_2601 dc_nc_2602 dc_nc_2603 dc_nc_2604 dc_nc_2605 dc_nc_2606 dc_nc_2607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
