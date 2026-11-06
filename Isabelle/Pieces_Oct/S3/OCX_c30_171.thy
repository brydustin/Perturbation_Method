theory OCX_c30_171
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2736: "oc_sub oc_b30 2736"
  by (oc_eval oc_c30_2736)

lemma oc_c30_2737: "oc_sub oc_b30 2737"
  by (oc_eval oc_c30_2737)

lemma oc_c30_2738: "oc_sub oc_b30 2738"
  by (oc_eval oc_c30_2738)

lemma oc_c30_2739: "oc_sub oc_b30 2739"
  by (oc_eval oc_c30_2739)

lemma oc_c30_2740: "oc_sub oc_b30 2740"
  by (oc_eval oc_c30_2740)

lemma oc_c30_2741: "oc_sub oc_b30 2741"
  by (oc_eval oc_c30_2741)

lemma oc_c30_2742: "oc_sub oc_b30 2742"
  by (oc_eval oc_c30_2742)

lemma oc_c30_2743: "oc_sub oc_b30 2743"
  by (oc_eval oc_c30_2743)

lemma oc_c30_2744: "oc_sub oc_b30 2744"
  by (oc_eval oc_c30_2744)

lemma oc_c30_2745: "oc_sub oc_b30 2745"
  by (oc_eval oc_c30_2745)

lemma oc_c30_2746: "oc_sub oc_b30 2746"
  by (oc_eval oc_c30_2746)

lemma oc_c30_2747: "oc_sub oc_b30 2747"
  by (oc_eval oc_c30_2747)

lemma oc_c30_2748: "oc_sub oc_b30 2748"
  by (oc_eval oc_c30_2748)

lemma oc_c30_2749: "oc_sub oc_b30 2749"
  by (oc_eval oc_c30_2749)

lemma oc_c30_2750: "oc_sub oc_b30 2750"
  by (oc_eval oc_c30_2750)

lemma oc_c30_2751: "oc_sub oc_b30 2751"
  by (oc_eval oc_c30_2751)

lemma upt_c30_171: "[2736..<2752] = [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]"
  by (simp add: upt_rec)

lemma sec_c30_171: "\<forall>j\<in>{16 * 171..<16 * 171 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 171..<16 * 171 + 16}"
  then have "j \<in> set [2736..<2752]" unfolding set_upt by simp
  then have "j \<in> set [2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751]" unfolding upt_c30_171 .
  then show "oc_sub oc_b30 j" using oc_c30_2736 oc_c30_2737 oc_c30_2738 oc_c30_2739 oc_c30_2740 oc_c30_2741 oc_c30_2742 oc_c30_2743 oc_c30_2744 oc_c30_2745 oc_c30_2746 oc_c30_2747 oc_c30_2748 oc_c30_2749 oc_c30_2750 oc_c30_2751
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
