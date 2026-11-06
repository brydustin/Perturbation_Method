theory DCX_nc_168
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2688: "dc_sub None 2688"
  by (dc_eval dc_nc_2688)

lemma dc_nc_2689: "dc_sub None 2689"
  by (dc_eval dc_nc_2689)

lemma dc_nc_2690: "dc_sub None 2690"
  by (dc_eval dc_nc_2690)

lemma dc_nc_2691: "dc_sub None 2691"
  by (dc_eval dc_nc_2691)

lemma dc_nc_2692: "dc_sub None 2692"
  by (dc_eval dc_nc_2692)

lemma dc_nc_2693: "dc_sub None 2693"
  by (dc_eval dc_nc_2693)

lemma dc_nc_2694: "dc_sub None 2694"
  by (dc_eval dc_nc_2694)

lemma dc_nc_2695: "dc_sub None 2695"
  by (dc_eval dc_nc_2695)

lemma dc_nc_2696: "dc_sub None 2696"
  by (dc_eval dc_nc_2696)

lemma dc_nc_2697: "dc_sub None 2697"
  by (dc_eval dc_nc_2697)

lemma dc_nc_2698: "dc_sub None 2698"
  by (dc_eval dc_nc_2698)

lemma dc_nc_2699: "dc_sub None 2699"
  by (dc_eval dc_nc_2699)

lemma dc_nc_2700: "dc_sub None 2700"
  by (dc_eval dc_nc_2700)

lemma dc_nc_2701: "dc_sub None 2701"
  by (dc_eval dc_nc_2701)

lemma dc_nc_2702: "dc_sub None 2702"
  by (dc_eval dc_nc_2702)

lemma dc_nc_2703: "dc_sub None 2703"
  by (dc_eval dc_nc_2703)

lemma upt_nc_168: "[2688..<2704] = [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]"
  by (simp add: upt_rec)

lemma sec_nc_168: "\<forall>j\<in>{16 * 168..<16 * 168 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 168..<16 * 168 + 16}"
  then have "j \<in> set [2688..<2704]" unfolding set_upt by simp
  then have "j \<in> set [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]" unfolding upt_nc_168 .
  then show "dc_sub None j" using dc_nc_2688 dc_nc_2689 dc_nc_2690 dc_nc_2691 dc_nc_2692 dc_nc_2693 dc_nc_2694 dc_nc_2695 dc_nc_2696 dc_nc_2697 dc_nc_2698 dc_nc_2699 dc_nc_2700 dc_nc_2701 dc_nc_2702 dc_nc_2703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
