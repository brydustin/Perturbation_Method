theory DCX_nc_171
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2736: "dc_sub None 2736"
  by (dc_eval dc_nc_2736)

lemma dc_nc_2737: "dc_sub None 2737"
  by (dc_eval dc_nc_2737)

lemma dc_nc_2738: "dc_sub None 2738"
  by (dc_eval dc_nc_2738)

lemma dc_nc_2739: "dc_sub None 2739"
  by (dc_eval dc_nc_2739)

lemma dc_nc_2740: "dc_sub None 2740"
  by (dc_eval dc_nc_2740)

lemma dc_nc_2741: "dc_sub None 2741"
  by (dc_eval dc_nc_2741)

lemma dc_nc_2742: "dc_sub None 2742"
  by (dc_eval dc_nc_2742)

lemma dc_nc_2743: "dc_sub None 2743"
  by (dc_eval dc_nc_2743)

lemma dc_nc_2744: "dc_sub None 2744"
  by (dc_eval dc_nc_2744)

lemma dc_nc_2745: "dc_sub None 2745"
  by (dc_eval dc_nc_2745)

lemma dc_nc_2746: "dc_sub None 2746"
  by (dc_eval dc_nc_2746)

lemma dc_nc_2747: "dc_sub None 2747"
  by (dc_eval dc_nc_2747)

lemma dc_nc_2748: "dc_sub None 2748"
  by (dc_eval dc_nc_2748)

lemma dc_nc_2749: "dc_sub None 2749"
  by (dc_eval dc_nc_2749)

lemma dc_nc_2750: "dc_sub None 2750"
  by (dc_eval dc_nc_2750)

lemma dc_nc_2751: "dc_sub None 2751"
  by (dc_eval dc_nc_2751)

lemma upt_nc_171: "[2736..<2752] = [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]"
  by (simp add: upt_rec)

lemma sec_nc_171: "\<forall>j\<in>{16 * 171..<16 * 171 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 171..<16 * 171 + 16}"
  then have "j \<in> set [2736..<2752]" unfolding set_upt by simp
  then have "j \<in> set [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]" unfolding upt_nc_171 .
  then show "dc_sub None j" using dc_nc_2736 dc_nc_2737 dc_nc_2738 dc_nc_2739 dc_nc_2740 dc_nc_2741 dc_nc_2742 dc_nc_2743 dc_nc_2744 dc_nc_2745 dc_nc_2746 dc_nc_2747 dc_nc_2748 dc_nc_2749 dc_nc_2750 dc_nc_2751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
