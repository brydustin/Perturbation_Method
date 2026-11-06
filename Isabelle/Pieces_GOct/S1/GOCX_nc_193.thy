theory GOCX_nc_193
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3088: "goc_sub None 3088"
  by (goc_eval goc_nc_3088)

lemma goc_nc_3089: "goc_sub None 3089"
  by (goc_eval goc_nc_3089)

lemma goc_nc_3090: "goc_sub None 3090"
  by (goc_eval goc_nc_3090)

lemma goc_nc_3091: "goc_sub None 3091"
  by (goc_eval goc_nc_3091)

lemma goc_nc_3092: "goc_sub None 3092"
  by (goc_eval goc_nc_3092)

lemma goc_nc_3093: "goc_sub None 3093"
  by (goc_eval goc_nc_3093)

lemma goc_nc_3094: "goc_sub None 3094"
  by (goc_eval goc_nc_3094)

lemma goc_nc_3095: "goc_sub None 3095"
  by (goc_eval goc_nc_3095)

lemma goc_nc_3096: "goc_sub None 3096"
  by (goc_eval goc_nc_3096)

lemma goc_nc_3097: "goc_sub None 3097"
  by (goc_eval goc_nc_3097)

lemma goc_nc_3098: "goc_sub None 3098"
  by (goc_eval goc_nc_3098)

lemma goc_nc_3099: "goc_sub None 3099"
  by (goc_eval goc_nc_3099)

lemma goc_nc_3100: "goc_sub None 3100"
  by (goc_eval goc_nc_3100)

lemma goc_nc_3101: "goc_sub None 3101"
  by (goc_eval goc_nc_3101)

lemma goc_nc_3102: "goc_sub None 3102"
  by (goc_eval goc_nc_3102)

lemma goc_nc_3103: "goc_sub None 3103"
  by (goc_eval goc_nc_3103)

lemma gupt_nc_193: "[3088..<3104] = [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]"
  by (simp add: upt_rec)

lemma gsec_nc_193: "\<forall>j\<in>{16 * 193..<16 * 193 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 193..<16 * 193 + 16}"
  then have "j \<in> set [3088..<3104]" unfolding set_upt by simp
  then have "j \<in> set [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]" unfolding gupt_nc_193 .
  then show "goc_sub None j" using goc_nc_3088 goc_nc_3089 goc_nc_3090 goc_nc_3091 goc_nc_3092 goc_nc_3093 goc_nc_3094 goc_nc_3095 goc_nc_3096 goc_nc_3097 goc_nc_3098 goc_nc_3099 goc_nc_3100 goc_nc_3101 goc_nc_3102 goc_nc_3103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
