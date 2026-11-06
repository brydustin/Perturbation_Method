theory OCX_c30_178
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2848: "oc_sub oc_b30 2848"
  by (oc_eval oc_c30_2848)

lemma oc_c30_2849: "oc_sub oc_b30 2849"
  by (oc_eval oc_c30_2849)

lemma oc_c30_2850: "oc_sub oc_b30 2850"
  by (oc_eval oc_c30_2850)

lemma oc_c30_2851: "oc_sub oc_b30 2851"
  by (oc_eval oc_c30_2851)

lemma oc_c30_2852: "oc_sub oc_b30 2852"
  by (oc_eval oc_c30_2852)

lemma oc_c30_2853: "oc_sub oc_b30 2853"
  by (oc_eval oc_c30_2853)

lemma oc_c30_2854: "oc_sub oc_b30 2854"
  by (oc_eval oc_c30_2854)

lemma oc_c30_2855: "oc_sub oc_b30 2855"
  by (oc_eval oc_c30_2855)

lemma oc_c30_2856: "oc_sub oc_b30 2856"
  by (oc_eval oc_c30_2856)

lemma oc_c30_2857: "oc_sub oc_b30 2857"
  by (oc_eval oc_c30_2857)

lemma oc_c30_2858: "oc_sub oc_b30 2858"
  by (oc_eval oc_c30_2858)

lemma oc_c30_2859: "oc_sub oc_b30 2859"
  by (oc_eval oc_c30_2859)

lemma oc_c30_2860: "oc_sub oc_b30 2860"
  by (oc_eval oc_c30_2860)

lemma oc_c30_2861: "oc_sub oc_b30 2861"
  by (oc_eval oc_c30_2861)

lemma oc_c30_2862: "oc_sub oc_b30 2862"
  by (oc_eval oc_c30_2862)

lemma oc_c30_2863: "oc_sub oc_b30 2863"
  by (oc_eval oc_c30_2863)

lemma upt_c30_178: "[2848..<2864] = [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]"
  by (simp add: upt_rec)

lemma sec_c30_178: "\<forall>j\<in>{16 * 178..<16 * 178 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 178..<16 * 178 + 16}"
  then have "j \<in> set [2848..<2864]" unfolding set_upt by simp
  then have "j \<in> set [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]" unfolding upt_c30_178 .
  then show "oc_sub oc_b30 j" using oc_c30_2848 oc_c30_2849 oc_c30_2850 oc_c30_2851 oc_c30_2852 oc_c30_2853 oc_c30_2854 oc_c30_2855 oc_c30_2856 oc_c30_2857 oc_c30_2858 oc_c30_2859 oc_c30_2860 oc_c30_2861 oc_c30_2862 oc_c30_2863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
