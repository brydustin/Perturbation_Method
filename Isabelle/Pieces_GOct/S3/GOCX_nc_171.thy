theory GOCX_nc_171
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2736: "goc_sub None 2736"
  by (goc_eval goc_nc_2736)

lemma goc_nc_2737: "goc_sub None 2737"
  by (goc_eval goc_nc_2737)

lemma goc_nc_2738: "goc_sub None 2738"
  by (goc_eval goc_nc_2738)

lemma goc_nc_2739: "goc_sub None 2739"
  by (goc_eval goc_nc_2739)

lemma goc_nc_2740: "goc_sub None 2740"
  by (goc_eval goc_nc_2740)

lemma goc_nc_2741: "goc_sub None 2741"
  by (goc_eval goc_nc_2741)

lemma goc_nc_2742: "goc_sub None 2742"
  by (goc_eval goc_nc_2742)

lemma goc_nc_2743: "goc_sub None 2743"
  by (goc_eval goc_nc_2743)

lemma goc_nc_2744: "goc_sub None 2744"
  by (goc_eval goc_nc_2744)

lemma goc_nc_2745: "goc_sub None 2745"
  by (goc_eval goc_nc_2745)

lemma goc_nc_2746: "goc_sub None 2746"
  by (goc_eval goc_nc_2746)

lemma goc_nc_2747: "goc_sub None 2747"
  by (goc_eval goc_nc_2747)

lemma goc_nc_2748: "goc_sub None 2748"
  by (goc_eval goc_nc_2748)

lemma goc_nc_2749: "goc_sub None 2749"
  by (goc_eval goc_nc_2749)

lemma goc_nc_2750: "goc_sub None 2750"
  by (goc_eval goc_nc_2750)

lemma goc_nc_2751: "goc_sub None 2751"
  by (goc_eval goc_nc_2751)

lemma gupt_nc_171: "[2736..<2752] = [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]"
  by (simp add: upt_rec)

lemma gsec_nc_171: "\<forall>j\<in>{16 * 171..<16 * 171 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 171..<16 * 171 + 16}"
  then have "j \<in> set [2736..<2752]" unfolding set_upt by simp
  then have "j \<in> set [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]" unfolding gupt_nc_171 .
  then show "goc_sub None j" using goc_nc_2736 goc_nc_2737 goc_nc_2738 goc_nc_2739 goc_nc_2740 goc_nc_2741 goc_nc_2742 goc_nc_2743 goc_nc_2744 goc_nc_2745 goc_nc_2746 goc_nc_2747 goc_nc_2748 goc_nc_2749 goc_nc_2750 goc_nc_2751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
