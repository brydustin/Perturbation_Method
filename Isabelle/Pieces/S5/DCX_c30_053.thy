theory DCX_c30_053
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0848: "dc_sub dc_b30 848"
  by (dc_eval dc_c30_0848)

lemma dc_c30_0849: "dc_sub dc_b30 849"
  by (dc_eval dc_c30_0849)

lemma dc_c30_0850: "dc_sub dc_b30 850"
  by (dc_eval dc_c30_0850)

lemma dc_c30_0851: "dc_sub dc_b30 851"
  by (dc_eval dc_c30_0851)

lemma dc_c30_0852: "dc_sub dc_b30 852"
  by (dc_eval dc_c30_0852)

lemma dc_c30_0853: "dc_sub dc_b30 853"
  by (dc_eval dc_c30_0853)

lemma dc_c30_0854: "dc_sub dc_b30 854"
  by (dc_eval dc_c30_0854)

lemma dc_c30_0855: "dc_sub dc_b30 855"
  by (dc_eval dc_c30_0855)

lemma dc_c30_0856: "dc_sub dc_b30 856"
  by (dc_eval dc_c30_0856)

lemma dc_c30_0857: "dc_sub dc_b30 857"
  by (dc_eval dc_c30_0857)

lemma dc_c30_0858: "dc_sub dc_b30 858"
  by (dc_eval dc_c30_0858)

lemma dc_c30_0859: "dc_sub dc_b30 859"
  by (dc_eval dc_c30_0859)

lemma dc_c30_0860: "dc_sub dc_b30 860"
  by (dc_eval dc_c30_0860)

lemma dc_c30_0861: "dc_sub dc_b30 861"
  by (dc_eval dc_c30_0861)

lemma dc_c30_0862: "dc_sub dc_b30 862"
  by (dc_eval dc_c30_0862)

lemma dc_c30_0863: "dc_sub dc_b30 863"
  by (dc_eval dc_c30_0863)

lemma upt_c30_053: "[848..<864] = [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]"
  by (simp add: upt_rec)

lemma sec_c30_053: "\<forall>j\<in>{16 * 53..<16 * 53 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 53..<16 * 53 + 16}"
  then have "j \<in> set [848..<864]" unfolding set_upt by simp
  then have "j \<in> set [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]" unfolding upt_c30_053 .
  then show "dc_sub dc_b30 j" using dc_c30_0848 dc_c30_0849 dc_c30_0850 dc_c30_0851 dc_c30_0852 dc_c30_0853 dc_c30_0854 dc_c30_0855 dc_c30_0856 dc_c30_0857 dc_c30_0858 dc_c30_0859 dc_c30_0860 dc_c30_0861 dc_c30_0862 dc_c30_0863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
