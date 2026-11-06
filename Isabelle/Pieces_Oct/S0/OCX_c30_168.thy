theory OCX_c30_168
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2688: "oc_sub oc_b30 2688"
  by (oc_eval oc_c30_2688)

lemma oc_c30_2689: "oc_sub oc_b30 2689"
  by (oc_eval oc_c30_2689)

lemma oc_c30_2690: "oc_sub oc_b30 2690"
  by (oc_eval oc_c30_2690)

lemma oc_c30_2691: "oc_sub oc_b30 2691"
  by (oc_eval oc_c30_2691)

lemma oc_c30_2692: "oc_sub oc_b30 2692"
  by (oc_eval oc_c30_2692)

lemma oc_c30_2693: "oc_sub oc_b30 2693"
  by (oc_eval oc_c30_2693)

lemma oc_c30_2694: "oc_sub oc_b30 2694"
  by (oc_eval oc_c30_2694)

lemma oc_c30_2695: "oc_sub oc_b30 2695"
  by (oc_eval oc_c30_2695)

lemma oc_c30_2696: "oc_sub oc_b30 2696"
  by (oc_eval oc_c30_2696)

lemma oc_c30_2697: "oc_sub oc_b30 2697"
  by (oc_eval oc_c30_2697)

lemma oc_c30_2698: "oc_sub oc_b30 2698"
  by (oc_eval oc_c30_2698)

lemma oc_c30_2699: "oc_sub oc_b30 2699"
  by (oc_eval oc_c30_2699)

lemma oc_c30_2700: "oc_sub oc_b30 2700"
  by (oc_eval oc_c30_2700)

lemma oc_c30_2701: "oc_sub oc_b30 2701"
  by (oc_eval oc_c30_2701)

lemma oc_c30_2702: "oc_sub oc_b30 2702"
  by (oc_eval oc_c30_2702)

lemma oc_c30_2703: "oc_sub oc_b30 2703"
  by (oc_eval oc_c30_2703)

lemma upt_c30_168: "[2688..<2704] = [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]"
  by (simp add: upt_rec)

lemma sec_c30_168: "\<forall>j\<in>{16 * 168..<16 * 168 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 168..<16 * 168 + 16}"
  then have "j \<in> set [2688..<2704]" unfolding set_upt by simp
  then have "j \<in> set [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]" unfolding upt_c30_168 .
  then show "oc_sub oc_b30 j" using oc_c30_2688 oc_c30_2689 oc_c30_2690 oc_c30_2691 oc_c30_2692 oc_c30_2693 oc_c30_2694 oc_c30_2695 oc_c30_2696 oc_c30_2697 oc_c30_2698 oc_c30_2699 oc_c30_2700 oc_c30_2701 oc_c30_2702 oc_c30_2703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
