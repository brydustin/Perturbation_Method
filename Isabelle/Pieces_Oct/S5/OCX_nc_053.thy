theory OCX_nc_053
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0848: "oc_sub None 848"
  by (oc_eval oc_nc_0848)

lemma oc_nc_0849: "oc_sub None 849"
  by (oc_eval oc_nc_0849)

lemma oc_nc_0850: "oc_sub None 850"
  by (oc_eval oc_nc_0850)

lemma oc_nc_0851: "oc_sub None 851"
  by (oc_eval oc_nc_0851)

lemma oc_nc_0852: "oc_sub None 852"
  by (oc_eval oc_nc_0852)

lemma oc_nc_0853: "oc_sub None 853"
  by (oc_eval oc_nc_0853)

lemma oc_nc_0854: "oc_sub None 854"
  by (oc_eval oc_nc_0854)

lemma oc_nc_0855: "oc_sub None 855"
  by (oc_eval oc_nc_0855)

lemma oc_nc_0856: "oc_sub None 856"
  by (oc_eval oc_nc_0856)

lemma oc_nc_0857: "oc_sub None 857"
  by (oc_eval oc_nc_0857)

lemma oc_nc_0858: "oc_sub None 858"
  by (oc_eval oc_nc_0858)

lemma oc_nc_0859: "oc_sub None 859"
  by (oc_eval oc_nc_0859)

lemma oc_nc_0860: "oc_sub None 860"
  by (oc_eval oc_nc_0860)

lemma oc_nc_0861: "oc_sub None 861"
  by (oc_eval oc_nc_0861)

lemma oc_nc_0862: "oc_sub None 862"
  by (oc_eval oc_nc_0862)

lemma oc_nc_0863: "oc_sub None 863"
  by (oc_eval oc_nc_0863)

lemma upt_nc_053: "[848..<864] = [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]"
  by (simp add: upt_rec)

lemma sec_nc_053: "\<forall>j\<in>{16 * 53..<16 * 53 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 53..<16 * 53 + 16}"
  then have "j \<in> set [848..<864]" unfolding set_upt by simp
  then have "j \<in> set [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]" unfolding upt_nc_053 .
  then show "oc_sub None j" using oc_nc_0848 oc_nc_0849 oc_nc_0850 oc_nc_0851 oc_nc_0852 oc_nc_0853 oc_nc_0854 oc_nc_0855 oc_nc_0856 oc_nc_0857 oc_nc_0858 oc_nc_0859 oc_nc_0860 oc_nc_0861 oc_nc_0862 oc_nc_0863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
