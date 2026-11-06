theory GDCX_nc_168
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2688: "gdc_sub None 2688"
  by (gdc_eval gdc_nc_2688)

lemma gdc_nc_2689: "gdc_sub None 2689"
  by (gdc_eval gdc_nc_2689)

lemma gdc_nc_2690: "gdc_sub None 2690"
  by (gdc_eval gdc_nc_2690)

lemma gdc_nc_2691: "gdc_sub None 2691"
  by (gdc_eval gdc_nc_2691)

lemma gdc_nc_2692: "gdc_sub None 2692"
  by (gdc_eval gdc_nc_2692)

lemma gdc_nc_2693: "gdc_sub None 2693"
  by (gdc_eval gdc_nc_2693)

lemma gdc_nc_2694: "gdc_sub None 2694"
  by (gdc_eval gdc_nc_2694)

lemma gdc_nc_2695: "gdc_sub None 2695"
  by (gdc_eval gdc_nc_2695)

lemma gdc_nc_2696: "gdc_sub None 2696"
  by (gdc_eval gdc_nc_2696)

lemma gdc_nc_2697: "gdc_sub None 2697"
  by (gdc_eval gdc_nc_2697)

lemma gdc_nc_2698: "gdc_sub None 2698"
  by (gdc_eval gdc_nc_2698)

lemma gdc_nc_2699: "gdc_sub None 2699"
  by (gdc_eval gdc_nc_2699)

lemma gdc_nc_2700: "gdc_sub None 2700"
  by (gdc_eval gdc_nc_2700)

lemma gdc_nc_2701: "gdc_sub None 2701"
  by (gdc_eval gdc_nc_2701)

lemma gdc_nc_2702: "gdc_sub None 2702"
  by (gdc_eval gdc_nc_2702)

lemma gdc_nc_2703: "gdc_sub None 2703"
  by (gdc_eval gdc_nc_2703)

lemma gupt_nc_168: "[2688..<2704] = [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]"
  by (simp add: upt_rec)

lemma gsec_nc_168: "\<forall>j\<in>{16 * 168..<16 * 168 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 168..<16 * 168 + 16}"
  then have "j \<in> set [2688..<2704]" unfolding set_upt by simp
  then have "j \<in> set [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]" unfolding gupt_nc_168 .
  then show "gdc_sub None j" using gdc_nc_2688 gdc_nc_2689 gdc_nc_2690 gdc_nc_2691 gdc_nc_2692 gdc_nc_2693 gdc_nc_2694 gdc_nc_2695 gdc_nc_2696 gdc_nc_2697 gdc_nc_2698 gdc_nc_2699 gdc_nc_2700 gdc_nc_2701 gdc_nc_2702 gdc_nc_2703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
