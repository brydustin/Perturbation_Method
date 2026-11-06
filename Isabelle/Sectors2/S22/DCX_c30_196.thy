theory DCX_c30_196
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3136: "dc_sub dc_b30 3136"
  by (dc_eval dc_c30_3136)

lemma dc_c30_3137: "dc_sub dc_b30 3137"
  by (dc_eval dc_c30_3137)

lemma dc_c30_3138: "dc_sub dc_b30 3138"
  by (dc_eval dc_c30_3138)

lemma dc_c30_3139: "dc_sub dc_b30 3139"
  by (dc_eval dc_c30_3139)

lemma dc_c30_3140: "dc_sub dc_b30 3140"
  by (dc_eval dc_c30_3140)

lemma dc_c30_3141: "dc_sub dc_b30 3141"
  by (dc_eval dc_c30_3141)

lemma dc_c30_3142: "dc_sub dc_b30 3142"
  by (dc_eval dc_c30_3142)

lemma dc_c30_3143: "dc_sub dc_b30 3143"
  by (dc_eval dc_c30_3143)

lemma dc_c30_3144: "dc_sub dc_b30 3144"
  by (dc_eval dc_c30_3144)

lemma dc_c30_3145: "dc_sub dc_b30 3145"
  by (dc_eval dc_c30_3145)

lemma dc_c30_3146: "dc_sub dc_b30 3146"
  by (dc_eval dc_c30_3146)

lemma dc_c30_3147: "dc_sub dc_b30 3147"
  by (dc_eval dc_c30_3147)

lemma dc_c30_3148: "dc_sub dc_b30 3148"
  by (dc_eval dc_c30_3148)

lemma dc_c30_3149: "dc_sub dc_b30 3149"
  by (dc_eval dc_c30_3149)

lemma dc_c30_3150: "dc_sub dc_b30 3150"
  by (dc_eval dc_c30_3150)

lemma dc_c30_3151: "dc_sub dc_b30 3151"
  by (dc_eval dc_c30_3151)

lemma upt_c30_196: "[3136..<3152] = [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]"
  by (simp add: upt_rec)

lemma sec_c30_196: "\<forall>j\<in>{16 * 196..<16 * 196 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 196..<16 * 196 + 16}"
  then have "j \<in> set [3136..<3152]" unfolding set_upt by simp
  then have "j \<in> set [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]" unfolding upt_c30_196 .
  then show "dc_sub dc_b30 j" using dc_c30_3136 dc_c30_3137 dc_c30_3138 dc_c30_3139 dc_c30_3140 dc_c30_3141 dc_c30_3142 dc_c30_3143 dc_c30_3144 dc_c30_3145 dc_c30_3146 dc_c30_3147 dc_c30_3148 dc_c30_3149 dc_c30_3150 dc_c30_3151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
