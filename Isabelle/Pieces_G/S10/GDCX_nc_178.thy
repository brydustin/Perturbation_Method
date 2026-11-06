theory GDCX_nc_178
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2848: "gdc_sub None 2848"
  by (gdc_eval gdc_nc_2848)

lemma gdc_nc_2849: "gdc_sub None 2849"
  by (gdc_eval gdc_nc_2849)

lemma gdc_nc_2850: "gdc_sub None 2850"
  by (gdc_eval gdc_nc_2850)

lemma gdc_nc_2851: "gdc_sub None 2851"
  by (gdc_eval gdc_nc_2851)

lemma gdc_nc_2852: "gdc_sub None 2852"
  by (gdc_eval gdc_nc_2852)

lemma gdc_nc_2853: "gdc_sub None 2853"
  by (gdc_eval gdc_nc_2853)

lemma gdc_nc_2854: "gdc_sub None 2854"
  by (gdc_eval gdc_nc_2854)

lemma gdc_nc_2855: "gdc_sub None 2855"
  by (gdc_eval gdc_nc_2855)

lemma gdc_nc_2856: "gdc_sub None 2856"
  by (gdc_eval gdc_nc_2856)

lemma gdc_nc_2857: "gdc_sub None 2857"
  by (gdc_eval gdc_nc_2857)

lemma gdc_nc_2858: "gdc_sub None 2858"
  by (gdc_eval gdc_nc_2858)

lemma gdc_nc_2859: "gdc_sub None 2859"
  by (gdc_eval gdc_nc_2859)

lemma gdc_nc_2860: "gdc_sub None 2860"
  by (gdc_eval gdc_nc_2860)

lemma gdc_nc_2861: "gdc_sub None 2861"
  by (gdc_eval gdc_nc_2861)

lemma gdc_nc_2862: "gdc_sub None 2862"
  by (gdc_eval gdc_nc_2862)

lemma gdc_nc_2863: "gdc_sub None 2863"
  by (gdc_eval gdc_nc_2863)

lemma gupt_nc_178: "[2848..<2864] = [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]"
  by (simp add: upt_rec)

lemma gsec_nc_178: "\<forall>j\<in>{16 * 178..<16 * 178 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 178..<16 * 178 + 16}"
  then have "j \<in> set [2848..<2864]" unfolding set_upt by simp
  then have "j \<in> set [2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863]" unfolding gupt_nc_178 .
  then show "gdc_sub None j" using gdc_nc_2848 gdc_nc_2849 gdc_nc_2850 gdc_nc_2851 gdc_nc_2852 gdc_nc_2853 gdc_nc_2854 gdc_nc_2855 gdc_nc_2856 gdc_nc_2857 gdc_nc_2858 gdc_nc_2859 gdc_nc_2860 gdc_nc_2861 gdc_nc_2862 gdc_nc_2863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
