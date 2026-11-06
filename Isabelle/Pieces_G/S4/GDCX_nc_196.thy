theory GDCX_nc_196
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3136: "gdc_sub None 3136"
  by (gdc_eval gdc_nc_3136)

lemma gdc_nc_3137: "gdc_sub None 3137"
  by (gdc_eval gdc_nc_3137)

lemma gdc_nc_3138: "gdc_sub None 3138"
  by (gdc_eval gdc_nc_3138)

lemma gdc_nc_3139: "gdc_sub None 3139"
  by (gdc_eval gdc_nc_3139)

lemma gdc_nc_3140: "gdc_sub None 3140"
  by (gdc_eval gdc_nc_3140)

lemma gdc_nc_3141: "gdc_sub None 3141"
  by (gdc_eval gdc_nc_3141)

lemma gdc_nc_3142: "gdc_sub None 3142"
  by (gdc_eval gdc_nc_3142)

lemma gdc_nc_3143: "gdc_sub None 3143"
  by (gdc_eval gdc_nc_3143)

lemma gdc_nc_3144: "gdc_sub None 3144"
  by (gdc_eval gdc_nc_3144)

lemma gdc_nc_3145: "gdc_sub None 3145"
  by (gdc_eval gdc_nc_3145)

lemma gdc_nc_3146: "gdc_sub None 3146"
  by (gdc_eval gdc_nc_3146)

lemma gdc_nc_3147: "gdc_sub None 3147"
  by (gdc_eval gdc_nc_3147)

lemma gdc_nc_3148: "gdc_sub None 3148"
  by (gdc_eval gdc_nc_3148)

lemma gdc_nc_3149: "gdc_sub None 3149"
  by (gdc_eval gdc_nc_3149)

lemma gdc_nc_3150: "gdc_sub None 3150"
  by (gdc_eval gdc_nc_3150)

lemma gdc_nc_3151: "gdc_sub None 3151"
  by (gdc_eval gdc_nc_3151)

lemma gupt_nc_196: "[3136..<3152] = [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]"
  by (simp add: upt_rec)

lemma gsec_nc_196: "\<forall>j\<in>{16 * 196..<16 * 196 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 196..<16 * 196 + 16}"
  then have "j \<in> set [3136..<3152]" unfolding set_upt by simp
  then have "j \<in> set [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]" unfolding gupt_nc_196 .
  then show "gdc_sub None j" using gdc_nc_3136 gdc_nc_3137 gdc_nc_3138 gdc_nc_3139 gdc_nc_3140 gdc_nc_3141 gdc_nc_3142 gdc_nc_3143 gdc_nc_3144 gdc_nc_3145 gdc_nc_3146 gdc_nc_3147 gdc_nc_3148 gdc_nc_3149 gdc_nc_3150 gdc_nc_3151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
