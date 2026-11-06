theory GDCX_nc_193
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3088: "gdc_sub None 3088"
  by (gdc_eval gdc_nc_3088)

lemma gdc_nc_3089: "gdc_sub None 3089"
  by (gdc_eval gdc_nc_3089)

lemma gdc_nc_3090: "gdc_sub None 3090"
  by (gdc_eval gdc_nc_3090)

lemma gdc_nc_3091: "gdc_sub None 3091"
  by (gdc_eval gdc_nc_3091)

lemma gdc_nc_3092: "gdc_sub None 3092"
  by (gdc_eval gdc_nc_3092)

lemma gdc_nc_3093: "gdc_sub None 3093"
  by (gdc_eval gdc_nc_3093)

lemma gdc_nc_3094: "gdc_sub None 3094"
  by (gdc_eval gdc_nc_3094)

lemma gdc_nc_3095: "gdc_sub None 3095"
  by (gdc_eval gdc_nc_3095)

lemma gdc_nc_3096: "gdc_sub None 3096"
  by (gdc_eval gdc_nc_3096)

lemma gdc_nc_3097: "gdc_sub None 3097"
  by (gdc_eval gdc_nc_3097)

lemma gdc_nc_3098: "gdc_sub None 3098"
  by (gdc_eval gdc_nc_3098)

lemma gdc_nc_3099: "gdc_sub None 3099"
  by (gdc_eval gdc_nc_3099)

lemma gdc_nc_3100: "gdc_sub None 3100"
  by (gdc_eval gdc_nc_3100)

lemma gdc_nc_3101: "gdc_sub None 3101"
  by (gdc_eval gdc_nc_3101)

lemma gdc_nc_3102: "gdc_sub None 3102"
  by (gdc_eval gdc_nc_3102)

lemma gdc_nc_3103: "gdc_sub None 3103"
  by (gdc_eval gdc_nc_3103)

lemma gupt_nc_193: "[3088..<3104] = [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]"
  by (simp add: upt_rec)

lemma gsec_nc_193: "\<forall>j\<in>{16 * 193..<16 * 193 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 193..<16 * 193 + 16}"
  then have "j \<in> set [3088..<3104]" unfolding set_upt by simp
  then have "j \<in> set [3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103]" unfolding gupt_nc_193 .
  then show "gdc_sub None j" using gdc_nc_3088 gdc_nc_3089 gdc_nc_3090 gdc_nc_3091 gdc_nc_3092 gdc_nc_3093 gdc_nc_3094 gdc_nc_3095 gdc_nc_3096 gdc_nc_3097 gdc_nc_3098 gdc_nc_3099 gdc_nc_3100 gdc_nc_3101 gdc_nc_3102 gdc_nc_3103
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
