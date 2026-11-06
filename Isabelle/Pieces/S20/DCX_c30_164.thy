theory DCX_c30_164
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2624: "dc_sub dc_b30 2624"
  by (dc_eval dc_c30_2624)

lemma dc_c30_2625: "dc_sub dc_b30 2625"
  by (dc_eval dc_c30_2625)

lemma dc_c30_2626: "dc_sub dc_b30 2626"
  by (dc_eval dc_c30_2626)

lemma dc_c30_2627: "dc_sub dc_b30 2627"
  by (dc_eval dc_c30_2627)

lemma dc_c30_2628: "dc_sub dc_b30 2628"
  by (dc_eval dc_c30_2628)

lemma dc_c30_2629: "dc_sub dc_b30 2629"
  by (dc_eval dc_c30_2629)

lemma dc_c30_2630: "dc_sub dc_b30 2630"
  by (dc_eval dc_c30_2630)

lemma dc_c30_2631: "dc_sub dc_b30 2631"
  by (dc_eval dc_c30_2631)

lemma dc_c30_2632: "dc_sub dc_b30 2632"
  by (dc_eval dc_c30_2632)

lemma dc_c30_2633: "dc_sub dc_b30 2633"
  by (dc_eval dc_c30_2633)

lemma dc_c30_2634: "dc_sub dc_b30 2634"
  by (dc_eval dc_c30_2634)

lemma dc_c30_2635: "dc_sub dc_b30 2635"
  by (dc_eval dc_c30_2635)

lemma dc_c30_2636: "dc_sub dc_b30 2636"
  by (dc_eval dc_c30_2636)

lemma dc_c30_2637: "dc_sub dc_b30 2637"
  by (dc_eval dc_c30_2637)

lemma dc_c30_2638: "dc_sub dc_b30 2638"
  by (dc_eval dc_c30_2638)

lemma dc_c30_2639: "dc_sub dc_b30 2639"
  by (dc_eval dc_c30_2639)

lemma upt_c30_164: "[2624..<2640] = [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]"
  by (simp add: upt_rec)

lemma sec_c30_164: "\<forall>j\<in>{16 * 164..<16 * 164 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 164..<16 * 164 + 16}"
  then have "j \<in> set [2624..<2640]" unfolding set_upt by simp
  then have "j \<in> set [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]" unfolding upt_c30_164 .
  then show "dc_sub dc_b30 j" using dc_c30_2624 dc_c30_2625 dc_c30_2626 dc_c30_2627 dc_c30_2628 dc_c30_2629 dc_c30_2630 dc_c30_2631 dc_c30_2632 dc_c30_2633 dc_c30_2634 dc_c30_2635 dc_c30_2636 dc_c30_2637 dc_c30_2638 dc_c30_2639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
