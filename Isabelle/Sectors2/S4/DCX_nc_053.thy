theory DCX_nc_053
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0848: "dc_sub None 848"
  by (dc_eval dc_nc_0848)

lemma dc_nc_0849: "dc_sub None 849"
  by (dc_eval dc_nc_0849)

lemma dc_nc_0850: "dc_sub None 850"
  by (dc_eval dc_nc_0850)

lemma dc_nc_0851: "dc_sub None 851"
  by (dc_eval dc_nc_0851)

lemma dc_nc_0852: "dc_sub None 852"
  by (dc_eval dc_nc_0852)

lemma dc_nc_0853: "dc_sub None 853"
  by (dc_eval dc_nc_0853)

lemma dc_nc_0854: "dc_sub None 854"
  by (dc_eval dc_nc_0854)

lemma dc_nc_0855: "dc_sub None 855"
  by (dc_eval dc_nc_0855)

lemma dc_nc_0856: "dc_sub None 856"
  by (dc_eval dc_nc_0856)

lemma dc_nc_0857: "dc_sub None 857"
  by (dc_eval dc_nc_0857)

lemma dc_nc_0858: "dc_sub None 858"
  by (dc_eval dc_nc_0858)

lemma dc_nc_0859: "dc_sub None 859"
  by (dc_eval dc_nc_0859)

lemma dc_nc_0860: "dc_sub None 860"
  by (dc_eval dc_nc_0860)

lemma dc_nc_0861: "dc_sub None 861"
  by (dc_eval dc_nc_0861)

lemma dc_nc_0862: "dc_sub None 862"
  by (dc_eval dc_nc_0862)

lemma dc_nc_0863: "dc_sub None 863"
  by (dc_eval dc_nc_0863)

lemma upt_nc_053: "[848..<864] = [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]"
  by (simp add: upt_rec)

lemma sec_nc_053: "\<forall>j\<in>{16 * 53..<16 * 53 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 53..<16 * 53 + 16}"
  then have "j \<in> set [848..<864]" unfolding set_upt by simp
  then have "j \<in> set [848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]" unfolding upt_nc_053 .
  then show "dc_sub None j" using dc_nc_0848 dc_nc_0849 dc_nc_0850 dc_nc_0851 dc_nc_0852 dc_nc_0853 dc_nc_0854 dc_nc_0855 dc_nc_0856 dc_nc_0857 dc_nc_0858 dc_nc_0859 dc_nc_0860 dc_nc_0861 dc_nc_0862 dc_nc_0863
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
