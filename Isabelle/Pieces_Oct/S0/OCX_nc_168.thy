theory OCX_nc_168
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2688: "oc_sub None 2688"
  by (oc_eval oc_nc_2688)

lemma oc_nc_2689: "oc_sub None 2689"
  by (oc_eval oc_nc_2689)

lemma oc_nc_2690: "oc_sub None 2690"
  by (oc_eval oc_nc_2690)

lemma oc_nc_2691: "oc_sub None 2691"
  by (oc_eval oc_nc_2691)

lemma oc_nc_2692: "oc_sub None 2692"
  by (oc_eval oc_nc_2692)

lemma oc_nc_2693: "oc_sub None 2693"
  by (oc_eval oc_nc_2693)

lemma oc_nc_2694: "oc_sub None 2694"
  by (oc_eval oc_nc_2694)

lemma oc_nc_2695: "oc_sub None 2695"
  by (oc_eval oc_nc_2695)

lemma oc_nc_2696: "oc_sub None 2696"
  by (oc_eval oc_nc_2696)

lemma oc_nc_2697: "oc_sub None 2697"
  by (oc_eval oc_nc_2697)

lemma oc_nc_2698: "oc_sub None 2698"
  by (oc_eval oc_nc_2698)

lemma oc_nc_2699: "oc_sub None 2699"
  by (oc_eval oc_nc_2699)

lemma oc_nc_2700: "oc_sub None 2700"
  by (oc_eval oc_nc_2700)

lemma oc_nc_2701: "oc_sub None 2701"
  by (oc_eval oc_nc_2701)

lemma oc_nc_2702: "oc_sub None 2702"
  by (oc_eval oc_nc_2702)

lemma oc_nc_2703: "oc_sub None 2703"
  by (oc_eval oc_nc_2703)

lemma upt_nc_168: "[2688..<2704] = [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]"
  by (simp add: upt_rec)

lemma sec_nc_168: "\<forall>j\<in>{16 * 168..<16 * 168 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 168..<16 * 168 + 16}"
  then have "j \<in> set [2688..<2704]" unfolding set_upt by simp
  then have "j \<in> set [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]" unfolding upt_nc_168 .
  then show "oc_sub None j" using oc_nc_2688 oc_nc_2689 oc_nc_2690 oc_nc_2691 oc_nc_2692 oc_nc_2693 oc_nc_2694 oc_nc_2695 oc_nc_2696 oc_nc_2697 oc_nc_2698 oc_nc_2699 oc_nc_2700 oc_nc_2701 oc_nc_2702 oc_nc_2703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
