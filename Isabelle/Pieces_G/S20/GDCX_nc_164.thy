theory GDCX_nc_164
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2624: "gdc_sub None 2624"
  by (gdc_eval gdc_nc_2624)

lemma gdc_nc_2625: "gdc_sub None 2625"
  by (gdc_eval gdc_nc_2625)

lemma gdc_nc_2626: "gdc_sub None 2626"
  by (gdc_eval gdc_nc_2626)

lemma gdc_nc_2627: "gdc_sub None 2627"
  by (gdc_eval gdc_nc_2627)

lemma gdc_nc_2628: "gdc_sub None 2628"
  by (gdc_eval gdc_nc_2628)

lemma gdc_nc_2629: "gdc_sub None 2629"
  by (gdc_eval gdc_nc_2629)

lemma gdc_nc_2630: "gdc_sub None 2630"
  by (gdc_eval gdc_nc_2630)

lemma gdc_nc_2631: "gdc_sub None 2631"
  by (gdc_eval gdc_nc_2631)

lemma gdc_nc_2632: "gdc_sub None 2632"
  by (gdc_eval gdc_nc_2632)

lemma gdc_nc_2633: "gdc_sub None 2633"
  by (gdc_eval gdc_nc_2633)

lemma gdc_nc_2634: "gdc_sub None 2634"
  by (gdc_eval gdc_nc_2634)

lemma gdc_nc_2635: "gdc_sub None 2635"
  by (gdc_eval gdc_nc_2635)

lemma gdc_nc_2636: "gdc_sub None 2636"
  by (gdc_eval gdc_nc_2636)

lemma gdc_nc_2637: "gdc_sub None 2637"
  by (gdc_eval gdc_nc_2637)

lemma gdc_nc_2638: "gdc_sub None 2638"
  by (gdc_eval gdc_nc_2638)

lemma gdc_nc_2639: "gdc_sub None 2639"
  by (gdc_eval gdc_nc_2639)

lemma gupt_nc_164: "[2624..<2640] = [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]"
  by (simp add: upt_rec)

lemma gsec_nc_164: "\<forall>j\<in>{16 * 164..<16 * 164 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 164..<16 * 164 + 16}"
  then have "j \<in> set [2624..<2640]" unfolding set_upt by simp
  then have "j \<in> set [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]" unfolding gupt_nc_164 .
  then show "gdc_sub None j" using gdc_nc_2624 gdc_nc_2625 gdc_nc_2626 gdc_nc_2627 gdc_nc_2628 gdc_nc_2629 gdc_nc_2630 gdc_nc_2631 gdc_nc_2632 gdc_nc_2633 gdc_nc_2634 gdc_nc_2635 gdc_nc_2636 gdc_nc_2637 gdc_nc_2638 gdc_nc_2639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
