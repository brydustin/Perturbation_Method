theory GOCX_nc_053
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0848: "goc_sub None 848"
  by (goc_eval goc_nc_0848)

lemma goc_nc_0849: "goc_sub None 849"
  by (goc_eval goc_nc_0849)

lemma goc_nc_0850: "goc_sub None 850"
  by (goc_eval goc_nc_0850)

lemma goc_nc_0851: "goc_sub None 851"
  by (goc_eval goc_nc_0851)

lemma goc_nc_0852: "goc_sub None 852"
  by (goc_eval goc_nc_0852)

lemma goc_nc_0853: "goc_sub None 853"
  by (goc_eval goc_nc_0853)

lemma goc_nc_0854: "goc_sub None 854"
  by (goc_eval goc_nc_0854)

lemma goc_nc_0855: "goc_sub None 855"
  by (goc_eval goc_nc_0855)

lemma goc_nc_0856: "goc_sub None 856"
  by (goc_eval goc_nc_0856)

lemma goc_nc_0857: "goc_sub None 857"
  by (goc_eval goc_nc_0857)

lemma goc_nc_0858: "goc_sub None 858"
  by (goc_eval goc_nc_0858)

lemma goc_nc_0859: "goc_sub None 859"
  by (goc_eval goc_nc_0859)

lemma goc_nc_0860: "goc_sub None 860"
  by (goc_eval goc_nc_0860)

lemma goc_nc_0861: "goc_sub None 861"
  by (goc_eval goc_nc_0861)

lemma goc_nc_0862: "goc_sub None 862"
  by (goc_eval goc_nc_0862)

lemma goc_nc_0863: "goc_sub None 863"
  by (goc_eval goc_nc_0863)

lemma gupt_nc_053: "[848..<864] = [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]"
  by (simp add: upt_rec)

lemma gsec_nc_053: "\<forall>j\<in>{16 * 53..<16 * 53 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 53..<16 * 53 + 16}"
  then have "j \<in> set [848..<864]" unfolding set_upt by simp
  then have "j \<in> set [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]" unfolding gupt_nc_053 .
  then show "goc_sub None j" using goc_nc_0848 goc_nc_0849 goc_nc_0850 goc_nc_0851 goc_nc_0852 goc_nc_0853 goc_nc_0854 goc_nc_0855 goc_nc_0856 goc_nc_0857 goc_nc_0858 goc_nc_0859 goc_nc_0860 goc_nc_0861 goc_nc_0862 goc_nc_0863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
