theory OCX_nc_196
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3136: "oc_sub None 3136"
  by (oc_eval oc_nc_3136)

lemma oc_nc_3137: "oc_sub None 3137"
  by (oc_eval oc_nc_3137)

lemma oc_nc_3138: "oc_sub None 3138"
  by (oc_eval oc_nc_3138)

lemma oc_nc_3139: "oc_sub None 3139"
  by (oc_eval oc_nc_3139)

lemma oc_nc_3140: "oc_sub None 3140"
  by (oc_eval oc_nc_3140)

lemma oc_nc_3141: "oc_sub None 3141"
  by (oc_eval oc_nc_3141)

lemma oc_nc_3142: "oc_sub None 3142"
  by (oc_eval oc_nc_3142)

lemma oc_nc_3143: "oc_sub None 3143"
  by (oc_eval oc_nc_3143)

lemma oc_nc_3144: "oc_sub None 3144"
  by (oc_eval oc_nc_3144)

lemma oc_nc_3145: "oc_sub None 3145"
  by (oc_eval oc_nc_3145)

lemma oc_nc_3146: "oc_sub None 3146"
  by (oc_eval oc_nc_3146)

lemma oc_nc_3147: "oc_sub None 3147"
  by (oc_eval oc_nc_3147)

lemma oc_nc_3148: "oc_sub None 3148"
  by (oc_eval oc_nc_3148)

lemma oc_nc_3149: "oc_sub None 3149"
  by (oc_eval oc_nc_3149)

lemma oc_nc_3150: "oc_sub None 3150"
  by (oc_eval oc_nc_3150)

lemma oc_nc_3151: "oc_sub None 3151"
  by (oc_eval oc_nc_3151)

lemma upt_nc_196: "[3136..<3152] = [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]"
  by (simp add: upt_rec)

lemma sec_nc_196: "\<forall>j\<in>{16 * 196..<16 * 196 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 196..<16 * 196 + 16}"
  then have "j \<in> set [3136..<3152]" unfolding set_upt by simp
  then have "j \<in> set [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]" unfolding upt_nc_196 .
  then show "oc_sub None j" using oc_nc_3136 oc_nc_3137 oc_nc_3138 oc_nc_3139 oc_nc_3140 oc_nc_3141 oc_nc_3142 oc_nc_3143 oc_nc_3144 oc_nc_3145 oc_nc_3146 oc_nc_3147 oc_nc_3148 oc_nc_3149 oc_nc_3150 oc_nc_3151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
