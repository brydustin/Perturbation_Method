theory DCX_c30_168
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2688: "dc_sub dc_b30 2688"
  by (dc_eval dc_c30_2688)

lemma dc_c30_2689: "dc_sub dc_b30 2689"
  by (dc_eval dc_c30_2689)

lemma dc_c30_2690: "dc_sub dc_b30 2690"
  by (dc_eval dc_c30_2690)

lemma dc_c30_2691: "dc_sub dc_b30 2691"
  by (dc_eval dc_c30_2691)

lemma dc_c30_2692: "dc_sub dc_b30 2692"
  by (dc_eval dc_c30_2692)

lemma dc_c30_2693: "dc_sub dc_b30 2693"
  by (dc_eval dc_c30_2693)

lemma dc_c30_2694: "dc_sub dc_b30 2694"
  by (dc_eval dc_c30_2694)

lemma dc_c30_2695: "dc_sub dc_b30 2695"
  by (dc_eval dc_c30_2695)

lemma dc_c30_2696: "dc_sub dc_b30 2696"
  by (dc_eval dc_c30_2696)

lemma dc_c30_2697: "dc_sub dc_b30 2697"
  by (dc_eval dc_c30_2697)

lemma dc_c30_2698: "dc_sub dc_b30 2698"
  by (dc_eval dc_c30_2698)

lemma dc_c30_2699: "dc_sub dc_b30 2699"
  by (dc_eval dc_c30_2699)

lemma dc_c30_2700: "dc_sub dc_b30 2700"
  by (dc_eval dc_c30_2700)

lemma dc_c30_2701: "dc_sub dc_b30 2701"
  by (dc_eval dc_c30_2701)

lemma dc_c30_2702: "dc_sub dc_b30 2702"
  by (dc_eval dc_c30_2702)

lemma dc_c30_2703: "dc_sub dc_b30 2703"
  by (dc_eval dc_c30_2703)

lemma upt_c30_168: "[2688..<2704] = [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]"
  by (simp add: upt_rec)

lemma sec_c30_168: "\<forall>j\<in>{16 * 168..<16 * 168 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 168..<16 * 168 + 16}"
  then have "j \<in> set [2688..<2704]" unfolding set_upt by simp
  then have "j \<in> set [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]" unfolding upt_c30_168 .
  then show "dc_sub dc_b30 j" using dc_c30_2688 dc_c30_2689 dc_c30_2690 dc_c30_2691 dc_c30_2692 dc_c30_2693 dc_c30_2694 dc_c30_2695 dc_c30_2696 dc_c30_2697 dc_c30_2698 dc_c30_2699 dc_c30_2700 dc_c30_2701 dc_c30_2702 dc_c30_2703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
