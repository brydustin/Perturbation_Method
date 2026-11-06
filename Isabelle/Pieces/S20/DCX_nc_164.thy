theory DCX_nc_164
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2624: "dc_sub None 2624"
  by (dc_eval dc_nc_2624)

lemma dc_nc_2625: "dc_sub None 2625"
  by (dc_eval dc_nc_2625)

lemma dc_nc_2626: "dc_sub None 2626"
  by (dc_eval dc_nc_2626)

lemma dc_nc_2627: "dc_sub None 2627"
  by (dc_eval dc_nc_2627)

lemma dc_nc_2628: "dc_sub None 2628"
  by (dc_eval dc_nc_2628)

lemma dc_nc_2629: "dc_sub None 2629"
  by (dc_eval dc_nc_2629)

lemma dc_nc_2630: "dc_sub None 2630"
  by (dc_eval dc_nc_2630)

lemma dc_nc_2631: "dc_sub None 2631"
  by (dc_eval dc_nc_2631)

lemma dc_nc_2632: "dc_sub None 2632"
  by (dc_eval dc_nc_2632)

lemma dc_nc_2633: "dc_sub None 2633"
  by (dc_eval dc_nc_2633)

lemma dc_nc_2634: "dc_sub None 2634"
  by (dc_eval dc_nc_2634)

lemma dc_nc_2635: "dc_sub None 2635"
  by (dc_eval dc_nc_2635)

lemma dc_nc_2636: "dc_sub None 2636"
  by (dc_eval dc_nc_2636)

lemma dc_nc_2637: "dc_sub None 2637"
  by (dc_eval dc_nc_2637)

lemma dc_nc_2638: "dc_sub None 2638"
  by (dc_eval dc_nc_2638)

lemma dc_nc_2639: "dc_sub None 2639"
  by (dc_eval dc_nc_2639)

lemma upt_nc_164: "[2624..<2640] = [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]"
  by (simp add: upt_rec)

lemma sec_nc_164: "\<forall>j\<in>{16 * 164..<16 * 164 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 164..<16 * 164 + 16}"
  then have "j \<in> set [2624..<2640]" unfolding set_upt by simp
  then have "j \<in> set [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]" unfolding upt_nc_164 .
  then show "dc_sub None j" using dc_nc_2624 dc_nc_2625 dc_nc_2626 dc_nc_2627 dc_nc_2628 dc_nc_2629 dc_nc_2630 dc_nc_2631 dc_nc_2632 dc_nc_2633 dc_nc_2634 dc_nc_2635 dc_nc_2636 dc_nc_2637 dc_nc_2638 dc_nc_2639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
