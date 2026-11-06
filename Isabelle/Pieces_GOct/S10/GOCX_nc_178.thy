theory GOCX_nc_178
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2848: "goc_sub None 2848"
  by (goc_eval goc_nc_2848)

lemma goc_nc_2849: "goc_sub None 2849"
  by (goc_eval goc_nc_2849)

lemma goc_nc_2850: "goc_sub None 2850"
  by (goc_eval goc_nc_2850)

lemma goc_nc_2851: "goc_sub None 2851"
  by (goc_eval goc_nc_2851)

lemma goc_nc_2852: "goc_sub None 2852"
  by (goc_eval goc_nc_2852)

lemma goc_nc_2853: "goc_sub None 2853"
  by (goc_eval goc_nc_2853)

lemma goc_nc_2854: "goc_sub None 2854"
  by (goc_eval goc_nc_2854)

lemma goc_nc_2855: "goc_sub None 2855"
  by (goc_eval goc_nc_2855)

lemma goc_nc_2856: "goc_sub None 2856"
  by (goc_eval goc_nc_2856)

lemma goc_nc_2857: "goc_sub None 2857"
  by (goc_eval goc_nc_2857)

lemma goc_nc_2858: "goc_sub None 2858"
  by (goc_eval goc_nc_2858)

lemma goc_nc_2859: "goc_sub None 2859"
  by (goc_eval goc_nc_2859)

lemma goc_nc_2860: "goc_sub None 2860"
  by (goc_eval goc_nc_2860)

lemma goc_nc_2861: "goc_sub None 2861"
  by (goc_eval goc_nc_2861)

lemma goc_nc_2862: "goc_sub None 2862"
  by (goc_eval goc_nc_2862)

lemma goc_nc_2863: "goc_sub None 2863"
  by (goc_eval goc_nc_2863)

lemma gupt_nc_178: "[2848..<2864] = [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]"
  by (simp add: upt_rec)

lemma gsec_nc_178: "\<forall>j\<in>{16 * 178..<16 * 178 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 178..<16 * 178 + 16}"
  then have "j \<in> set [2848..<2864]" unfolding set_upt by simp
  then have "j \<in> set [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]" unfolding gupt_nc_178 .
  then show "goc_sub None j" using goc_nc_2848 goc_nc_2849 goc_nc_2850 goc_nc_2851 goc_nc_2852 goc_nc_2853 goc_nc_2854 goc_nc_2855 goc_nc_2856 goc_nc_2857 goc_nc_2858 goc_nc_2859 goc_nc_2860 goc_nc_2861 goc_nc_2862 goc_nc_2863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
