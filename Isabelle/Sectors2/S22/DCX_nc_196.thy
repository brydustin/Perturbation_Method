theory DCX_nc_196
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3136: "dc_sub None 3136"
  by (dc_eval dc_nc_3136)

lemma dc_nc_3137: "dc_sub None 3137"
  by (dc_eval dc_nc_3137)

lemma dc_nc_3138: "dc_sub None 3138"
  by (dc_eval dc_nc_3138)

lemma dc_nc_3139: "dc_sub None 3139"
  by (dc_eval dc_nc_3139)

lemma dc_nc_3140: "dc_sub None 3140"
  by (dc_eval dc_nc_3140)

lemma dc_nc_3141: "dc_sub None 3141"
  by (dc_eval dc_nc_3141)

lemma dc_nc_3142: "dc_sub None 3142"
  by (dc_eval dc_nc_3142)

lemma dc_nc_3143: "dc_sub None 3143"
  by (dc_eval dc_nc_3143)

lemma dc_nc_3144: "dc_sub None 3144"
  by (dc_eval dc_nc_3144)

lemma dc_nc_3145: "dc_sub None 3145"
  by (dc_eval dc_nc_3145)

lemma dc_nc_3146: "dc_sub None 3146"
  by (dc_eval dc_nc_3146)

lemma dc_nc_3147: "dc_sub None 3147"
  by (dc_eval dc_nc_3147)

lemma dc_nc_3148: "dc_sub None 3148"
  by (dc_eval dc_nc_3148)

lemma dc_nc_3149: "dc_sub None 3149"
  by (dc_eval dc_nc_3149)

lemma dc_nc_3150: "dc_sub None 3150"
  by (dc_eval dc_nc_3150)

lemma dc_nc_3151: "dc_sub None 3151"
  by (dc_eval dc_nc_3151)

lemma upt_nc_196: "[3136..<3152] = [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]"
  by (simp add: upt_rec)

lemma sec_nc_196: "\<forall>j\<in>{16 * 196..<16 * 196 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 196..<16 * 196 + 16}"
  then have "j \<in> set [3136..<3152]" unfolding set_upt by simp
  then have "j \<in> set [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]" unfolding upt_nc_196 .
  then show "dc_sub None j" using dc_nc_3136 dc_nc_3137 dc_nc_3138 dc_nc_3139 dc_nc_3140 dc_nc_3141 dc_nc_3142 dc_nc_3143 dc_nc_3144 dc_nc_3145 dc_nc_3146 dc_nc_3147 dc_nc_3148 dc_nc_3149 dc_nc_3150 dc_nc_3151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
