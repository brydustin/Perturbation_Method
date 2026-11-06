theory GDCX_nc_162
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2592: "gdc_sub None 2592"
  by (gdc_eval gdc_nc_2592)

lemma gdc_nc_2593: "gdc_sub None 2593"
  by (gdc_eval gdc_nc_2593)

lemma gdc_nc_2594: "gdc_sub None 2594"
  by (gdc_eval gdc_nc_2594)

lemma gdc_nc_2595: "gdc_sub None 2595"
  by (gdc_eval gdc_nc_2595)

lemma gdc_nc_2596: "gdc_sub None 2596"
  by (gdc_eval gdc_nc_2596)

lemma gdc_nc_2597: "gdc_sub None 2597"
  by (gdc_eval gdc_nc_2597)

lemma gdc_nc_2598: "gdc_sub None 2598"
  by (gdc_eval gdc_nc_2598)

lemma gdc_nc_2599: "gdc_sub None 2599"
  by (gdc_eval gdc_nc_2599)

lemma gdc_nc_2600: "gdc_sub None 2600"
  by (gdc_eval gdc_nc_2600)

lemma gdc_nc_2601: "gdc_sub None 2601"
  by (gdc_eval gdc_nc_2601)

lemma gdc_nc_2602: "gdc_sub None 2602"
  by (gdc_eval gdc_nc_2602)

lemma gdc_nc_2603: "gdc_sub None 2603"
  by (gdc_eval gdc_nc_2603)

lemma gdc_nc_2604: "gdc_sub None 2604"
  by (gdc_eval gdc_nc_2604)

lemma gdc_nc_2605: "gdc_sub None 2605"
  by (gdc_eval gdc_nc_2605)

lemma gdc_nc_2606: "gdc_sub None 2606"
  by (gdc_eval gdc_nc_2606)

lemma gdc_nc_2607: "gdc_sub None 2607"
  by (gdc_eval gdc_nc_2607)

lemma gupt_nc_162: "[2592..<2608] = [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]"
  by (simp add: upt_rec)

lemma gsec_nc_162: "\<forall>j\<in>{16 * 162..<16 * 162 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 162..<16 * 162 + 16}"
  then have "j \<in> set [2592..<2608]" unfolding set_upt by simp
  then have "j \<in> set [2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2607]" unfolding gupt_nc_162 .
  then show "gdc_sub None j" using gdc_nc_2592 gdc_nc_2593 gdc_nc_2594 gdc_nc_2595 gdc_nc_2596 gdc_nc_2597 gdc_nc_2598 gdc_nc_2599 gdc_nc_2600 gdc_nc_2601 gdc_nc_2602 gdc_nc_2603 gdc_nc_2604 gdc_nc_2605 gdc_nc_2606 gdc_nc_2607
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
