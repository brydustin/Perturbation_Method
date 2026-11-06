theory DCX_nc_178
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2848: "dc_sub None 2848"
  by (dc_eval dc_nc_2848)

lemma dc_nc_2849: "dc_sub None 2849"
  by (dc_eval dc_nc_2849)

lemma dc_nc_2850: "dc_sub None 2850"
  by (dc_eval dc_nc_2850)

lemma dc_nc_2851: "dc_sub None 2851"
  by (dc_eval dc_nc_2851)

lemma dc_nc_2852: "dc_sub None 2852"
  by (dc_eval dc_nc_2852)

lemma dc_nc_2853: "dc_sub None 2853"
  by (dc_eval dc_nc_2853)

lemma dc_nc_2854: "dc_sub None 2854"
  by (dc_eval dc_nc_2854)

lemma dc_nc_2855: "dc_sub None 2855"
  by (dc_eval dc_nc_2855)

lemma dc_nc_2856: "dc_sub None 2856"
  by (dc_eval dc_nc_2856)

lemma dc_nc_2857: "dc_sub None 2857"
  by (dc_eval dc_nc_2857)

lemma dc_nc_2858: "dc_sub None 2858"
  by (dc_eval dc_nc_2858)

lemma dc_nc_2859: "dc_sub None 2859"
  by (dc_eval dc_nc_2859)

lemma dc_nc_2860: "dc_sub None 2860"
  by (dc_eval dc_nc_2860)

lemma dc_nc_2861: "dc_sub None 2861"
  by (dc_eval dc_nc_2861)

lemma dc_nc_2862: "dc_sub None 2862"
  by (dc_eval dc_nc_2862)

lemma dc_nc_2863: "dc_sub None 2863"
  by (dc_eval dc_nc_2863)

lemma upt_nc_178: "[2848..<2864] = [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]"
  by (simp add: upt_rec)

lemma sec_nc_178: "\<forall>j\<in>{16 * 178..<16 * 178 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 178..<16 * 178 + 16}"
  then have "j \<in> set [2848..<2864]" unfolding set_upt by simp
  then have "j \<in> set [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]" unfolding upt_nc_178 .
  then show "dc_sub None j" using dc_nc_2848 dc_nc_2849 dc_nc_2850 dc_nc_2851 dc_nc_2852 dc_nc_2853 dc_nc_2854 dc_nc_2855 dc_nc_2856 dc_nc_2857 dc_nc_2858 dc_nc_2859 dc_nc_2860 dc_nc_2861 dc_nc_2862 dc_nc_2863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
