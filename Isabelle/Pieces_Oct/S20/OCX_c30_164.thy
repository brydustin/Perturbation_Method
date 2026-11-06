theory OCX_c30_164
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2624: "oc_sub oc_b30 2624"
  by (oc_eval oc_c30_2624)

lemma oc_c30_2625: "oc_sub oc_b30 2625"
  by (oc_eval oc_c30_2625)

lemma oc_c30_2626: "oc_sub oc_b30 2626"
  by (oc_eval oc_c30_2626)

lemma oc_c30_2627: "oc_sub oc_b30 2627"
  by (oc_eval oc_c30_2627)

lemma oc_c30_2628: "oc_sub oc_b30 2628"
  by (oc_eval oc_c30_2628)

lemma oc_c30_2629: "oc_sub oc_b30 2629"
  by (oc_eval oc_c30_2629)

lemma oc_c30_2630: "oc_sub oc_b30 2630"
  by (oc_eval oc_c30_2630)

lemma oc_c30_2631: "oc_sub oc_b30 2631"
  by (oc_eval oc_c30_2631)

lemma oc_c30_2632: "oc_sub oc_b30 2632"
  by (oc_eval oc_c30_2632)

lemma oc_c30_2633: "oc_sub oc_b30 2633"
  by (oc_eval oc_c30_2633)

lemma oc_c30_2634: "oc_sub oc_b30 2634"
  by (oc_eval oc_c30_2634)

lemma oc_c30_2635: "oc_sub oc_b30 2635"
  by (oc_eval oc_c30_2635)

lemma oc_c30_2636: "oc_sub oc_b30 2636"
  by (oc_eval oc_c30_2636)

lemma oc_c30_2637: "oc_sub oc_b30 2637"
  by (oc_eval oc_c30_2637)

lemma oc_c30_2638: "oc_sub oc_b30 2638"
  by (oc_eval oc_c30_2638)

lemma oc_c30_2639: "oc_sub oc_b30 2639"
  by (oc_eval oc_c30_2639)

lemma upt_c30_164: "[2624..<2640] = [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]"
  by (simp add: upt_rec)

lemma sec_c30_164: "\<forall>j\<in>{16 * 164..<16 * 164 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 164..<16 * 164 + 16}"
  then have "j \<in> set [2624..<2640]" unfolding set_upt by simp
  then have "j \<in> set [2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2633, 2634, 2635, 2636, 2637, 2638, 2639]" unfolding upt_c30_164 .
  then show "oc_sub oc_b30 j" using oc_c30_2624 oc_c30_2625 oc_c30_2626 oc_c30_2627 oc_c30_2628 oc_c30_2629 oc_c30_2630 oc_c30_2631 oc_c30_2632 oc_c30_2633 oc_c30_2634 oc_c30_2635 oc_c30_2636 oc_c30_2637 oc_c30_2638 oc_c30_2639
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
