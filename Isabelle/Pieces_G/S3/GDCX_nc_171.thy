theory GDCX_nc_171
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2736: "gdc_sub None 2736"
  by (gdc_eval gdc_nc_2736)

lemma gdc_nc_2737: "gdc_sub None 2737"
  by (gdc_eval gdc_nc_2737)

lemma gdc_nc_2738: "gdc_sub None 2738"
  by (gdc_eval gdc_nc_2738)

lemma gdc_nc_2739: "gdc_sub None 2739"
  by (gdc_eval gdc_nc_2739)

lemma gdc_nc_2740: "gdc_sub None 2740"
  by (gdc_eval gdc_nc_2740)

lemma gdc_nc_2741: "gdc_sub None 2741"
  by (gdc_eval gdc_nc_2741)

lemma gdc_nc_2742: "gdc_sub None 2742"
  by (gdc_eval gdc_nc_2742)

lemma gdc_nc_2743: "gdc_sub None 2743"
  by (gdc_eval gdc_nc_2743)

lemma gdc_nc_2744: "gdc_sub None 2744"
  by (gdc_eval gdc_nc_2744)

lemma gdc_nc_2745: "gdc_sub None 2745"
  by (gdc_eval gdc_nc_2745)

lemma gdc_nc_2746: "gdc_sub None 2746"
  by (gdc_eval gdc_nc_2746)

lemma gdc_nc_2747: "gdc_sub None 2747"
  by (gdc_eval gdc_nc_2747)

lemma gdc_nc_2748: "gdc_sub None 2748"
  by (gdc_eval gdc_nc_2748)

lemma gdc_nc_2749: "gdc_sub None 2749"
  by (gdc_eval gdc_nc_2749)

lemma gdc_nc_2750: "gdc_sub None 2750"
  by (gdc_eval gdc_nc_2750)

lemma gdc_nc_2751: "gdc_sub None 2751"
  by (gdc_eval gdc_nc_2751)

lemma gupt_nc_171: "[2736..<2752] = [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]"
  by (simp add: upt_rec)

lemma gsec_nc_171: "\<forall>j\<in>{16 * 171..<16 * 171 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 171..<16 * 171 + 16}"
  then have "j \<in> set [2736..<2752]" unfolding set_upt by simp
  then have "j \<in> set [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]" unfolding gupt_nc_171 .
  then show "gdc_sub None j" using gdc_nc_2736 gdc_nc_2737 gdc_nc_2738 gdc_nc_2739 gdc_nc_2740 gdc_nc_2741 gdc_nc_2742 gdc_nc_2743 gdc_nc_2744 gdc_nc_2745 gdc_nc_2746 gdc_nc_2747 gdc_nc_2748 gdc_nc_2749 gdc_nc_2750 gdc_nc_2751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
