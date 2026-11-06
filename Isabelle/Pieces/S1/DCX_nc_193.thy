theory DCX_nc_193
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3088: "dc_sub None 3088"
  by (dc_eval dc_nc_3088)

lemma dc_nc_3089: "dc_sub None 3089"
  by (dc_eval dc_nc_3089)

lemma dc_nc_3090: "dc_sub None 3090"
  by (dc_eval dc_nc_3090)

lemma dc_nc_3091: "dc_sub None 3091"
  by (dc_eval dc_nc_3091)

lemma dc_nc_3092: "dc_sub None 3092"
  by (dc_eval dc_nc_3092)

lemma dc_nc_3093: "dc_sub None 3093"
  by (dc_eval dc_nc_3093)

lemma dc_nc_3094: "dc_sub None 3094"
  by (dc_eval dc_nc_3094)

lemma dc_nc_3095: "dc_sub None 3095"
  by (dc_eval dc_nc_3095)

lemma dc_nc_3096: "dc_sub None 3096"
  by (dc_eval dc_nc_3096)

lemma dc_nc_3097: "dc_sub None 3097"
  by (dc_eval dc_nc_3097)

lemma dc_nc_3098: "dc_sub None 3098"
  by (dc_eval dc_nc_3098)

lemma dc_nc_3099: "dc_sub None 3099"
  by (dc_eval dc_nc_3099)

lemma dc_nc_3100: "dc_sub None 3100"
  by (dc_eval dc_nc_3100)

lemma dc_nc_3101: "dc_sub None 3101"
  by (dc_eval dc_nc_3101)

lemma dc_nc_3102: "dc_sub None 3102"
  by (dc_eval dc_nc_3102)

lemma dc_nc_3103: "dc_sub None 3103"
  by (dc_eval dc_nc_3103)

lemma upt_nc_193: "[3088..<3104] = [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]"
  by (simp add: upt_rec)

lemma sec_nc_193: "\<forall>j\<in>{16 * 193..<16 * 193 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 193..<16 * 193 + 16}"
  then have "j \<in> set [3088..<3104]" unfolding set_upt by simp
  then have "j \<in> set [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]" unfolding upt_nc_193 .
  then show "dc_sub None j" using dc_nc_3088 dc_nc_3089 dc_nc_3090 dc_nc_3091 dc_nc_3092 dc_nc_3093 dc_nc_3094 dc_nc_3095 dc_nc_3096 dc_nc_3097 dc_nc_3098 dc_nc_3099 dc_nc_3100 dc_nc_3101 dc_nc_3102 dc_nc_3103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
