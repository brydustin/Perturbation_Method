theory OCX_nc_193
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3088: "oc_sub None 3088"
  by (oc_eval oc_nc_3088)

lemma oc_nc_3089: "oc_sub None 3089"
  by (oc_eval oc_nc_3089)

lemma oc_nc_3090: "oc_sub None 3090"
  by (oc_eval oc_nc_3090)

lemma oc_nc_3091: "oc_sub None 3091"
  by (oc_eval oc_nc_3091)

lemma oc_nc_3092: "oc_sub None 3092"
  by (oc_eval oc_nc_3092)

lemma oc_nc_3093: "oc_sub None 3093"
  by (oc_eval oc_nc_3093)

lemma oc_nc_3094: "oc_sub None 3094"
  by (oc_eval oc_nc_3094)

lemma oc_nc_3095: "oc_sub None 3095"
  by (oc_eval oc_nc_3095)

lemma oc_nc_3096: "oc_sub None 3096"
  by (oc_eval oc_nc_3096)

lemma oc_nc_3097: "oc_sub None 3097"
  by (oc_eval oc_nc_3097)

lemma oc_nc_3098: "oc_sub None 3098"
  by (oc_eval oc_nc_3098)

lemma oc_nc_3099: "oc_sub None 3099"
  by (oc_eval oc_nc_3099)

lemma oc_nc_3100: "oc_sub None 3100"
  by (oc_eval oc_nc_3100)

lemma oc_nc_3101: "oc_sub None 3101"
  by (oc_eval oc_nc_3101)

lemma oc_nc_3102: "oc_sub None 3102"
  by (oc_eval oc_nc_3102)

lemma oc_nc_3103: "oc_sub None 3103"
  by (oc_eval oc_nc_3103)

lemma upt_nc_193: "[3088..<3104] = [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]"
  by (simp add: upt_rec)

lemma sec_nc_193: "\<forall>j\<in>{16 * 193..<16 * 193 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 193..<16 * 193 + 16}"
  then have "j \<in> set [3088..<3104]" unfolding set_upt by simp
  then have "j \<in> set [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]" unfolding upt_nc_193 .
  then show "oc_sub None j" using oc_nc_3088 oc_nc_3089 oc_nc_3090 oc_nc_3091 oc_nc_3092 oc_nc_3093 oc_nc_3094 oc_nc_3095 oc_nc_3096 oc_nc_3097 oc_nc_3098 oc_nc_3099 oc_nc_3100 oc_nc_3101 oc_nc_3102 oc_nc_3103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
