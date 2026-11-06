theory GDCX_nc_053
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0848: "gdc_sub None 848"
  by (gdc_eval gdc_nc_0848)

lemma gdc_nc_0849: "gdc_sub None 849"
  by (gdc_eval gdc_nc_0849)

lemma gdc_nc_0850: "gdc_sub None 850"
  by (gdc_eval gdc_nc_0850)

lemma gdc_nc_0851: "gdc_sub None 851"
  by (gdc_eval gdc_nc_0851)

lemma gdc_nc_0852: "gdc_sub None 852"
  by (gdc_eval gdc_nc_0852)

lemma gdc_nc_0853: "gdc_sub None 853"
  by (gdc_eval gdc_nc_0853)

lemma gdc_nc_0854: "gdc_sub None 854"
  by (gdc_eval gdc_nc_0854)

lemma gdc_nc_0855: "gdc_sub None 855"
  by (gdc_eval gdc_nc_0855)

lemma gdc_nc_0856: "gdc_sub None 856"
  by (gdc_eval gdc_nc_0856)

lemma gdc_nc_0857: "gdc_sub None 857"
  by (gdc_eval gdc_nc_0857)

lemma gdc_nc_0858: "gdc_sub None 858"
  by (gdc_eval gdc_nc_0858)

lemma gdc_nc_0859: "gdc_sub None 859"
  by (gdc_eval gdc_nc_0859)

lemma gdc_nc_0860: "gdc_sub None 860"
  by (gdc_eval gdc_nc_0860)

lemma gdc_nc_0861: "gdc_sub None 861"
  by (gdc_eval gdc_nc_0861)

lemma gdc_nc_0862: "gdc_sub None 862"
  by (gdc_eval gdc_nc_0862)

lemma gdc_nc_0863: "gdc_sub None 863"
  by (gdc_eval gdc_nc_0863)

lemma gupt_nc_053: "[848..<864] = [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]"
  by (simp add: upt_rec)

lemma gsec_nc_053: "\<forall>j\<in>{16 * 53..<16 * 53 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 53..<16 * 53 + 16}"
  then have "j \<in> set [848..<864]" unfolding set_upt by simp
  then have "j \<in> set [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]" unfolding gupt_nc_053 .
  then show "gdc_sub None j" using gdc_nc_0848 gdc_nc_0849 gdc_nc_0850 gdc_nc_0851 gdc_nc_0852 gdc_nc_0853 gdc_nc_0854 gdc_nc_0855 gdc_nc_0856 gdc_nc_0857 gdc_nc_0858 gdc_nc_0859 gdc_nc_0860 gdc_nc_0861 gdc_nc_0862 gdc_nc_0863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
