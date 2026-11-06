theory OCX_c30_053
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0848: "oc_sub oc_b30 848"
  by (oc_eval oc_c30_0848)

lemma oc_c30_0849: "oc_sub oc_b30 849"
  by (oc_eval oc_c30_0849)

lemma oc_c30_0850: "oc_sub oc_b30 850"
  by (oc_eval oc_c30_0850)

lemma oc_c30_0851: "oc_sub oc_b30 851"
  by (oc_eval oc_c30_0851)

lemma oc_c30_0852: "oc_sub oc_b30 852"
  by (oc_eval oc_c30_0852)

lemma oc_c30_0853: "oc_sub oc_b30 853"
  by (oc_eval oc_c30_0853)

lemma oc_c30_0854: "oc_sub oc_b30 854"
  by (oc_eval oc_c30_0854)

lemma oc_c30_0855: "oc_sub oc_b30 855"
  by (oc_eval oc_c30_0855)

lemma oc_c30_0856: "oc_sub oc_b30 856"
  by (oc_eval oc_c30_0856)

lemma oc_c30_0857: "oc_sub oc_b30 857"
  by (oc_eval oc_c30_0857)

lemma oc_c30_0858: "oc_sub oc_b30 858"
  by (oc_eval oc_c30_0858)

lemma oc_c30_0859: "oc_sub oc_b30 859"
  by (oc_eval oc_c30_0859)

lemma oc_c30_0860: "oc_sub oc_b30 860"
  by (oc_eval oc_c30_0860)

lemma oc_c30_0861: "oc_sub oc_b30 861"
  by (oc_eval oc_c30_0861)

lemma oc_c30_0862: "oc_sub oc_b30 862"
  by (oc_eval oc_c30_0862)

lemma oc_c30_0863: "oc_sub oc_b30 863"
  by (oc_eval oc_c30_0863)

lemma upt_c30_053: "[848..<864] = [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]"
  by (simp add: upt_rec)

lemma sec_c30_053: "\<forall>j\<in>{16 * 53..<16 * 53 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 53..<16 * 53 + 16}"
  then have "j \<in> set [848..<864]" unfolding set_upt by simp
  then have "j \<in> set [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]" unfolding upt_c30_053 .
  then show "oc_sub oc_b30 j" using oc_c30_0848 oc_c30_0849 oc_c30_0850 oc_c30_0851 oc_c30_0852 oc_c30_0853 oc_c30_0854 oc_c30_0855 oc_c30_0856 oc_c30_0857 oc_c30_0858 oc_c30_0859 oc_c30_0860 oc_c30_0861 oc_c30_0862 oc_c30_0863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
