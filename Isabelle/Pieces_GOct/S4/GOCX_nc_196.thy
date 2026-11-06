theory GOCX_nc_196
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3136: "goc_sub None 3136"
  by (goc_eval goc_nc_3136)

lemma goc_nc_3137: "goc_sub None 3137"
  by (goc_eval goc_nc_3137)

lemma goc_nc_3138: "goc_sub None 3138"
  by (goc_eval goc_nc_3138)

lemma goc_nc_3139: "goc_sub None 3139"
  by (goc_eval goc_nc_3139)

lemma goc_nc_3140: "goc_sub None 3140"
  by (goc_eval goc_nc_3140)

lemma goc_nc_3141: "goc_sub None 3141"
  by (goc_eval goc_nc_3141)

lemma goc_nc_3142: "goc_sub None 3142"
  by (goc_eval goc_nc_3142)

lemma goc_nc_3143: "goc_sub None 3143"
  by (goc_eval goc_nc_3143)

lemma goc_nc_3144: "goc_sub None 3144"
  by (goc_eval goc_nc_3144)

lemma goc_nc_3145: "goc_sub None 3145"
  by (goc_eval goc_nc_3145)

lemma goc_nc_3146: "goc_sub None 3146"
  by (goc_eval goc_nc_3146)

lemma goc_nc_3147: "goc_sub None 3147"
  by (goc_eval goc_nc_3147)

lemma goc_nc_3148: "goc_sub None 3148"
  by (goc_eval goc_nc_3148)

lemma goc_nc_3149: "goc_sub None 3149"
  by (goc_eval goc_nc_3149)

lemma goc_nc_3150: "goc_sub None 3150"
  by (goc_eval goc_nc_3150)

lemma goc_nc_3151: "goc_sub None 3151"
  by (goc_eval goc_nc_3151)

lemma gupt_nc_196: "[3136..<3152] = [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]"
  by (simp add: upt_rec)

lemma gsec_nc_196: "\<forall>j\<in>{16 * 196..<16 * 196 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 196..<16 * 196 + 16}"
  then have "j \<in> set [3136..<3152]" unfolding set_upt by simp
  then have "j \<in> set [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]" unfolding gupt_nc_196 .
  then show "goc_sub None j" using goc_nc_3136 goc_nc_3137 goc_nc_3138 goc_nc_3139 goc_nc_3140 goc_nc_3141 goc_nc_3142 goc_nc_3143 goc_nc_3144 goc_nc_3145 goc_nc_3146 goc_nc_3147 goc_nc_3148 goc_nc_3149 goc_nc_3150 goc_nc_3151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
