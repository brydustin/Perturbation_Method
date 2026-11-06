theory GOCX_nc_168
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2688: "goc_sub None 2688"
  by (goc_eval goc_nc_2688)

lemma goc_nc_2689: "goc_sub None 2689"
  by (goc_eval goc_nc_2689)

lemma goc_nc_2690: "goc_sub None 2690"
  by (goc_eval goc_nc_2690)

lemma goc_nc_2691: "goc_sub None 2691"
  by (goc_eval goc_nc_2691)

lemma goc_nc_2692: "goc_sub None 2692"
  by (goc_eval goc_nc_2692)

lemma goc_nc_2693: "goc_sub None 2693"
  by (goc_eval goc_nc_2693)

lemma goc_nc_2694: "goc_sub None 2694"
  by (goc_eval goc_nc_2694)

lemma goc_nc_2695: "goc_sub None 2695"
  by (goc_eval goc_nc_2695)

lemma goc_nc_2696: "goc_sub None 2696"
  by (goc_eval goc_nc_2696)

lemma goc_nc_2697: "goc_sub None 2697"
  by (goc_eval goc_nc_2697)

lemma goc_nc_2698: "goc_sub None 2698"
  by (goc_eval goc_nc_2698)

lemma goc_nc_2699: "goc_sub None 2699"
  by (goc_eval goc_nc_2699)

lemma goc_nc_2700: "goc_sub None 2700"
  by (goc_eval goc_nc_2700)

lemma goc_nc_2701: "goc_sub None 2701"
  by (goc_eval goc_nc_2701)

lemma goc_nc_2702: "goc_sub None 2702"
  by (goc_eval goc_nc_2702)

lemma goc_nc_2703: "goc_sub None 2703"
  by (goc_eval goc_nc_2703)

lemma gupt_nc_168: "[2688..<2704] = [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]"
  by (simp add: upt_rec)

lemma gsec_nc_168: "\<forall>j\<in>{16 * 168..<16 * 168 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 168..<16 * 168 + 16}"
  then have "j \<in> set [2688..<2704]" unfolding set_upt by simp
  then have "j \<in> set [2688, 2689, 2690, 2691, 2692, 2693, 2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703]" unfolding gupt_nc_168 .
  then show "goc_sub None j" using goc_nc_2688 goc_nc_2689 goc_nc_2690 goc_nc_2691 goc_nc_2692 goc_nc_2693 goc_nc_2694 goc_nc_2695 goc_nc_2696 goc_nc_2697 goc_nc_2698 goc_nc_2699 goc_nc_2700 goc_nc_2701 goc_nc_2702 goc_nc_2703
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
