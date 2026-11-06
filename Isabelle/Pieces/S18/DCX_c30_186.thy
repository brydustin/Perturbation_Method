theory DCX_c30_186
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2976: "dc_sub dc_b30 2976"
  by (dc_eval dc_c30_2976)

lemma dc_c30_2977: "dc_sub dc_b30 2977"
  by (dc_eval dc_c30_2977)

lemma dc_c30_2978: "dc_sub dc_b30 2978"
  by (dc_eval dc_c30_2978)

lemma dc_c30_2979: "dc_sub dc_b30 2979"
  by (dc_eval dc_c30_2979)

lemma dc_c30_2980: "dc_sub dc_b30 2980"
  by (dc_eval dc_c30_2980)

lemma dc_c30_2981: "dc_sub dc_b30 2981"
  by (dc_eval dc_c30_2981)

lemma dc_c30_2982: "dc_sub dc_b30 2982"
  by (dc_eval dc_c30_2982)

lemma dc_c30_2983: "dc_sub dc_b30 2983"
  by (dc_eval dc_c30_2983)

lemma dc_c30_2984: "dc_sub dc_b30 2984"
  by (dc_eval dc_c30_2984)

lemma dc_c30_2985: "dc_sub dc_b30 2985"
  by (dc_eval dc_c30_2985)

lemma dc_c30_2986: "dc_sub dc_b30 2986"
  by (dc_eval dc_c30_2986)

lemma dc_c30_2987: "dc_sub dc_b30 2987"
  by (dc_eval dc_c30_2987)

lemma dc_c30_2988: "dc_sub dc_b30 2988"
  by (dc_eval dc_c30_2988)

lemma dc_c30_2989: "dc_sub dc_b30 2989"
  by (dc_eval dc_c30_2989)

lemma dc_c30_2990: "dc_sub dc_b30 2990"
  by (dc_eval dc_c30_2990)

lemma dc_c30_2991: "dc_sub dc_b30 2991"
  by (dc_eval dc_c30_2991)

lemma upt_c30_186: "[2976..<2992] = [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]"
  by (simp add: upt_rec)

lemma sec_c30_186: "\<forall>j\<in>{16 * 186..<16 * 186 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 186..<16 * 186 + 16}"
  then have "j \<in> set [2976..<2992]" unfolding set_upt by simp
  then have "j \<in> set [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]" unfolding upt_c30_186 .
  then show "dc_sub dc_b30 j" using dc_c30_2976 dc_c30_2977 dc_c30_2978 dc_c30_2979 dc_c30_2980 dc_c30_2981 dc_c30_2982 dc_c30_2983 dc_c30_2984 dc_c30_2985 dc_c30_2986 dc_c30_2987 dc_c30_2988 dc_c30_2989 dc_c30_2990 dc_c30_2991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
