theory DCX_c30_193
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3088: "dc_sub dc_b30 3088"
  by (dc_eval dc_c30_3088)

lemma dc_c30_3089: "dc_sub dc_b30 3089"
  by (dc_eval dc_c30_3089)

lemma dc_c30_3090: "dc_sub dc_b30 3090"
  by (dc_eval dc_c30_3090)

lemma dc_c30_3091: "dc_sub dc_b30 3091"
  by (dc_eval dc_c30_3091)

lemma dc_c30_3092: "dc_sub dc_b30 3092"
  by (dc_eval dc_c30_3092)

lemma dc_c30_3093: "dc_sub dc_b30 3093"
  by (dc_eval dc_c30_3093)

lemma dc_c30_3094: "dc_sub dc_b30 3094"
  by (dc_eval dc_c30_3094)

lemma dc_c30_3095: "dc_sub dc_b30 3095"
  by (dc_eval dc_c30_3095)

lemma dc_c30_3096: "dc_sub dc_b30 3096"
  by (dc_eval dc_c30_3096)

lemma dc_c30_3097: "dc_sub dc_b30 3097"
  by (dc_eval dc_c30_3097)

lemma dc_c30_3098: "dc_sub dc_b30 3098"
  by (dc_eval dc_c30_3098)

lemma dc_c30_3099: "dc_sub dc_b30 3099"
  by (dc_eval dc_c30_3099)

lemma dc_c30_3100: "dc_sub dc_b30 3100"
  by (dc_eval dc_c30_3100)

lemma dc_c30_3101: "dc_sub dc_b30 3101"
  by (dc_eval dc_c30_3101)

lemma dc_c30_3102: "dc_sub dc_b30 3102"
  by (dc_eval dc_c30_3102)

lemma dc_c30_3103: "dc_sub dc_b30 3103"
  by (dc_eval dc_c30_3103)

lemma upt_c30_193: "[3088..<3104] = [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]"
  by (simp add: upt_rec)

lemma sec_c30_193: "\<forall>j\<in>{16 * 193..<16 * 193 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 193..<16 * 193 + 16}"
  then have "j \<in> set [3088..<3104]" unfolding set_upt by simp
  then have "j \<in> set [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]" unfolding upt_c30_193 .
  then show "dc_sub dc_b30 j" using dc_c30_3088 dc_c30_3089 dc_c30_3090 dc_c30_3091 dc_c30_3092 dc_c30_3093 dc_c30_3094 dc_c30_3095 dc_c30_3096 dc_c30_3097 dc_c30_3098 dc_c30_3099 dc_c30_3100 dc_c30_3101 dc_c30_3102 dc_c30_3103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
