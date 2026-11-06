theory GOCX_nc_162
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2592: "goc_sub None 2592"
  by (goc_eval goc_nc_2592)

lemma goc_nc_2593: "goc_sub None 2593"
  by (goc_eval goc_nc_2593)

lemma goc_nc_2594: "goc_sub None 2594"
  by (goc_eval goc_nc_2594)

lemma goc_nc_2595: "goc_sub None 2595"
  by (goc_eval goc_nc_2595)

lemma goc_nc_2596: "goc_sub None 2596"
  by (goc_eval goc_nc_2596)

lemma goc_nc_2597: "goc_sub None 2597"
  by (goc_eval goc_nc_2597)

lemma goc_nc_2598: "goc_sub None 2598"
  by (goc_eval goc_nc_2598)

lemma goc_nc_2599: "goc_sub None 2599"
  by (goc_eval goc_nc_2599)

lemma goc_nc_2600: "goc_sub None 2600"
  by (goc_eval goc_nc_2600)

lemma goc_nc_2601: "goc_sub None 2601"
  by (goc_eval goc_nc_2601)

lemma goc_nc_2602: "goc_sub None 2602"
  by (goc_eval goc_nc_2602)

lemma goc_nc_2603: "goc_sub None 2603"
  by (goc_eval goc_nc_2603)

lemma goc_nc_2604: "goc_sub None 2604"
  by (goc_eval goc_nc_2604)

lemma goc_nc_2605: "goc_sub None 2605"
  by (goc_eval goc_nc_2605)

lemma goc_nc_2606: "goc_sub None 2606"
  by (goc_eval goc_nc_2606)

lemma goc_nc_2607: "goc_sub None 2607"
  by (goc_eval goc_nc_2607)

lemma gupt_nc_162: "[2592..<2608] = [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]"
  by (simp add: upt_rec)

lemma gsec_nc_162: "\<forall>j\<in>{16 * 162..<16 * 162 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 162..<16 * 162 + 16}"
  then have "j \<in> set [2592..<2608]" unfolding set_upt by simp
  then have "j \<in> set [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]" unfolding gupt_nc_162 .
  then show "goc_sub None j" using goc_nc_2592 goc_nc_2593 goc_nc_2594 goc_nc_2595 goc_nc_2596 goc_nc_2597 goc_nc_2598 goc_nc_2599 goc_nc_2600 goc_nc_2601 goc_nc_2602 goc_nc_2603 goc_nc_2604 goc_nc_2605 goc_nc_2606 goc_nc_2607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
