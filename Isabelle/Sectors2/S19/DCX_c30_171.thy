theory DCX_c30_171
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2736: "dc_sub dc_b30 2736"
  by (dc_eval dc_c30_2736)

lemma dc_c30_2737: "dc_sub dc_b30 2737"
  by (dc_eval dc_c30_2737)

lemma dc_c30_2738: "dc_sub dc_b30 2738"
  by (dc_eval dc_c30_2738)

lemma dc_c30_2739: "dc_sub dc_b30 2739"
  by (dc_eval dc_c30_2739)

lemma dc_c30_2740: "dc_sub dc_b30 2740"
  by (dc_eval dc_c30_2740)

lemma dc_c30_2741: "dc_sub dc_b30 2741"
  by (dc_eval dc_c30_2741)

lemma dc_c30_2742: "dc_sub dc_b30 2742"
  by (dc_eval dc_c30_2742)

lemma dc_c30_2743: "dc_sub dc_b30 2743"
  by (dc_eval dc_c30_2743)

lemma dc_c30_2744: "dc_sub dc_b30 2744"
  by (dc_eval dc_c30_2744)

lemma dc_c30_2745: "dc_sub dc_b30 2745"
  by (dc_eval dc_c30_2745)

lemma dc_c30_2746: "dc_sub dc_b30 2746"
  by (dc_eval dc_c30_2746)

lemma dc_c30_2747: "dc_sub dc_b30 2747"
  by (dc_eval dc_c30_2747)

lemma dc_c30_2748: "dc_sub dc_b30 2748"
  by (dc_eval dc_c30_2748)

lemma dc_c30_2749: "dc_sub dc_b30 2749"
  by (dc_eval dc_c30_2749)

lemma dc_c30_2750: "dc_sub dc_b30 2750"
  by (dc_eval dc_c30_2750)

lemma dc_c30_2751: "dc_sub dc_b30 2751"
  by (dc_eval dc_c30_2751)

lemma upt_c30_171: "[2736..<2752] = [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]"
  by (simp add: upt_rec)

lemma sec_c30_171: "\<forall>j\<in>{16 * 171..<16 * 171 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 171..<16 * 171 + 16}"
  then have "j \<in> set [2736..<2752]" unfolding set_upt by simp
  then have "j \<in> set [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]" unfolding upt_c30_171 .
  then show "dc_sub dc_b30 j" using dc_c30_2736 dc_c30_2737 dc_c30_2738 dc_c30_2739 dc_c30_2740 dc_c30_2741 dc_c30_2742 dc_c30_2743 dc_c30_2744 dc_c30_2745 dc_c30_2746 dc_c30_2747 dc_c30_2748 dc_c30_2749 dc_c30_2750 dc_c30_2751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
