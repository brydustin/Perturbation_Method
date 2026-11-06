theory OCX_c30_186
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2976: "oc_sub oc_b30 2976"
  by (oc_eval oc_c30_2976)

lemma oc_c30_2977: "oc_sub oc_b30 2977"
  by (oc_eval oc_c30_2977)

lemma oc_c30_2978: "oc_sub oc_b30 2978"
  by (oc_eval oc_c30_2978)

lemma oc_c30_2979: "oc_sub oc_b30 2979"
  by (oc_eval oc_c30_2979)

lemma oc_c30_2980: "oc_sub oc_b30 2980"
  by (oc_eval oc_c30_2980)

lemma oc_c30_2981: "oc_sub oc_b30 2981"
  by (oc_eval oc_c30_2981)

lemma oc_c30_2982: "oc_sub oc_b30 2982"
  by (oc_eval oc_c30_2982)

lemma oc_c30_2983: "oc_sub oc_b30 2983"
  by (oc_eval oc_c30_2983)

lemma oc_c30_2984: "oc_sub oc_b30 2984"
  by (oc_eval oc_c30_2984)

lemma oc_c30_2985: "oc_sub oc_b30 2985"
  by (oc_eval oc_c30_2985)

lemma oc_c30_2986: "oc_sub oc_b30 2986"
  by (oc_eval oc_c30_2986)

lemma oc_c30_2987: "oc_sub oc_b30 2987"
  by (oc_eval oc_c30_2987)

lemma oc_c30_2988: "oc_sub oc_b30 2988"
  by (oc_eval oc_c30_2988)

lemma oc_c30_2989: "oc_sub oc_b30 2989"
  by (oc_eval oc_c30_2989)

lemma oc_c30_2990: "oc_sub oc_b30 2990"
  by (oc_eval oc_c30_2990)

lemma oc_c30_2991: "oc_sub oc_b30 2991"
  by (oc_eval oc_c30_2991)

lemma upt_c30_186: "[2976..<2992] = [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]"
  by (simp add: upt_rec)

lemma sec_c30_186: "\<forall>j\<in>{16 * 186..<16 * 186 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 186..<16 * 186 + 16}"
  then have "j \<in> set [2976..<2992]" unfolding set_upt by simp
  then have "j \<in> set [2976, 2977, 2978, 2979, 2980, 2981, 2982, 2983, 2984, 2985, 2986, 2987, 2988, 2989, 2990, 2991]" unfolding upt_c30_186 .
  then show "oc_sub oc_b30 j" using oc_c30_2976 oc_c30_2977 oc_c30_2978 oc_c30_2979 oc_c30_2980 oc_c30_2981 oc_c30_2982 oc_c30_2983 oc_c30_2984 oc_c30_2985 oc_c30_2986 oc_c30_2987 oc_c30_2988 oc_c30_2989 oc_c30_2990 oc_c30_2991
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
