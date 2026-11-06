theory OCX_c30_196
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3136: "oc_sub oc_b30 3136"
  by (oc_eval oc_c30_3136)

lemma oc_c30_3137: "oc_sub oc_b30 3137"
  by (oc_eval oc_c30_3137)

lemma oc_c30_3138: "oc_sub oc_b30 3138"
  by (oc_eval oc_c30_3138)

lemma oc_c30_3139: "oc_sub oc_b30 3139"
  by (oc_eval oc_c30_3139)

lemma oc_c30_3140: "oc_sub oc_b30 3140"
  by (oc_eval oc_c30_3140)

lemma oc_c30_3141: "oc_sub oc_b30 3141"
  by (oc_eval oc_c30_3141)

lemma oc_c30_3142: "oc_sub oc_b30 3142"
  by (oc_eval oc_c30_3142)

lemma oc_c30_3143: "oc_sub oc_b30 3143"
  by (oc_eval oc_c30_3143)

lemma oc_c30_3144: "oc_sub oc_b30 3144"
  by (oc_eval oc_c30_3144)

lemma oc_c30_3145: "oc_sub oc_b30 3145"
  by (oc_eval oc_c30_3145)

lemma oc_c30_3146: "oc_sub oc_b30 3146"
  by (oc_eval oc_c30_3146)

lemma oc_c30_3147: "oc_sub oc_b30 3147"
  by (oc_eval oc_c30_3147)

lemma oc_c30_3148: "oc_sub oc_b30 3148"
  by (oc_eval oc_c30_3148)

lemma oc_c30_3149: "oc_sub oc_b30 3149"
  by (oc_eval oc_c30_3149)

lemma oc_c30_3150: "oc_sub oc_b30 3150"
  by (oc_eval oc_c30_3150)

lemma oc_c30_3151: "oc_sub oc_b30 3151"
  by (oc_eval oc_c30_3151)

lemma upt_c30_196: "[3136..<3152] = [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]"
  by (simp add: upt_rec)

lemma sec_c30_196: "\<forall>j\<in>{16 * 196..<16 * 196 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 196..<16 * 196 + 16}"
  then have "j \<in> set [3136..<3152]" unfolding set_upt by simp
  then have "j \<in> set [3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151]" unfolding upt_c30_196 .
  then show "oc_sub oc_b30 j" using oc_c30_3136 oc_c30_3137 oc_c30_3138 oc_c30_3139 oc_c30_3140 oc_c30_3141 oc_c30_3142 oc_c30_3143 oc_c30_3144 oc_c30_3145 oc_c30_3146 oc_c30_3147 oc_c30_3148 oc_c30_3149 oc_c30_3150 oc_c30_3151
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
