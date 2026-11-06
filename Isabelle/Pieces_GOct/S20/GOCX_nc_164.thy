theory GOCX_nc_164
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2624: "goc_sub None 2624"
  by (goc_eval goc_nc_2624)

lemma goc_nc_2625: "goc_sub None 2625"
  by (goc_eval goc_nc_2625)

lemma goc_nc_2626: "goc_sub None 2626"
  by (goc_eval goc_nc_2626)

lemma goc_nc_2627: "goc_sub None 2627"
  by (goc_eval goc_nc_2627)

lemma goc_nc_2628: "goc_sub None 2628"
  by (goc_eval goc_nc_2628)

lemma goc_nc_2629: "goc_sub None 2629"
  by (goc_eval goc_nc_2629)

lemma goc_nc_2630: "goc_sub None 2630"
  by (goc_eval goc_nc_2630)

lemma goc_nc_2631: "goc_sub None 2631"
  by (goc_eval goc_nc_2631)

lemma goc_nc_2632: "goc_sub None 2632"
  by (goc_eval goc_nc_2632)

lemma goc_nc_2633: "goc_sub None 2633"
  by (goc_eval goc_nc_2633)

lemma goc_nc_2634: "goc_sub None 2634"
  by (goc_eval goc_nc_2634)

lemma goc_nc_2635: "goc_sub None 2635"
  by (goc_eval goc_nc_2635)

lemma goc_nc_2636: "goc_sub None 2636"
  by (goc_eval goc_nc_2636)

lemma goc_nc_2637: "goc_sub None 2637"
  by (goc_eval goc_nc_2637)

lemma goc_nc_2638: "goc_sub None 2638"
  by (goc_eval goc_nc_2638)

lemma goc_nc_2639: "goc_sub None 2639"
  by (goc_eval goc_nc_2639)

lemma gupt_nc_164: "[2624..<2640] = [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]"
  by (simp add: upt_rec)

lemma gsec_nc_164: "\<forall>j\<in>{16 * 164..<16 * 164 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 164..<16 * 164 + 16}"
  then have "j \<in> set [2624..<2640]" unfolding set_upt by simp
  then have "j \<in> set [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]" unfolding gupt_nc_164 .
  then show "goc_sub None j" using goc_nc_2624 goc_nc_2625 goc_nc_2626 goc_nc_2627 goc_nc_2628 goc_nc_2629 goc_nc_2630 goc_nc_2631 goc_nc_2632 goc_nc_2633 goc_nc_2634 goc_nc_2635 goc_nc_2636 goc_nc_2637 goc_nc_2638 goc_nc_2639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
