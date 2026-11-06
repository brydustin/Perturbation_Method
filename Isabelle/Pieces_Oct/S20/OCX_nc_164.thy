theory OCX_nc_164
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2624: "oc_sub None 2624"
  by (oc_eval oc_nc_2624)

lemma oc_nc_2625: "oc_sub None 2625"
  by (oc_eval oc_nc_2625)

lemma oc_nc_2626: "oc_sub None 2626"
  by (oc_eval oc_nc_2626)

lemma oc_nc_2627: "oc_sub None 2627"
  by (oc_eval oc_nc_2627)

lemma oc_nc_2628: "oc_sub None 2628"
  by (oc_eval oc_nc_2628)

lemma oc_nc_2629: "oc_sub None 2629"
  by (oc_eval oc_nc_2629)

lemma oc_nc_2630: "oc_sub None 2630"
  by (oc_eval oc_nc_2630)

lemma oc_nc_2631: "oc_sub None 2631"
  by (oc_eval oc_nc_2631)

lemma oc_nc_2632: "oc_sub None 2632"
  by (oc_eval oc_nc_2632)

lemma oc_nc_2633: "oc_sub None 2633"
  by (oc_eval oc_nc_2633)

lemma oc_nc_2634: "oc_sub None 2634"
  by (oc_eval oc_nc_2634)

lemma oc_nc_2635: "oc_sub None 2635"
  by (oc_eval oc_nc_2635)

lemma oc_nc_2636: "oc_sub None 2636"
  by (oc_eval oc_nc_2636)

lemma oc_nc_2637: "oc_sub None 2637"
  by (oc_eval oc_nc_2637)

lemma oc_nc_2638: "oc_sub None 2638"
  by (oc_eval oc_nc_2638)

lemma oc_nc_2639: "oc_sub None 2639"
  by (oc_eval oc_nc_2639)

lemma upt_nc_164: "[2624..<2640] = [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]"
  by (simp add: upt_rec)

lemma sec_nc_164: "\<forall>j\<in>{16 * 164..<16 * 164 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 164..<16 * 164 + 16}"
  then have "j \<in> set [2624..<2640]" unfolding set_upt by simp
  then have "j \<in> set [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]" unfolding upt_nc_164 .
  then show "oc_sub None j" using oc_nc_2624 oc_nc_2625 oc_nc_2626 oc_nc_2627 oc_nc_2628 oc_nc_2629 oc_nc_2630 oc_nc_2631 oc_nc_2632 oc_nc_2633 oc_nc_2634 oc_nc_2635 oc_nc_2636 oc_nc_2637 oc_nc_2638 oc_nc_2639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
