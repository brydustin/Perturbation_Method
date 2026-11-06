theory OCX_c30_198
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3168: "oc_sub oc_b30 3168"
  by (oc_eval oc_c30_3168)

lemma oc_c30_3169: "oc_sub oc_b30 3169"
  by (oc_eval oc_c30_3169)

lemma oc_c30_3170: "oc_sub oc_b30 3170"
  by (oc_eval oc_c30_3170)

lemma oc_c30_3171: "oc_sub oc_b30 3171"
  by (oc_eval oc_c30_3171)

lemma oc_c30_3172: "oc_sub oc_b30 3172"
  by (oc_eval oc_c30_3172)

lemma oc_c30_3173: "oc_sub oc_b30 3173"
  by (oc_eval oc_c30_3173)

lemma oc_c30_3174: "oc_sub oc_b30 3174"
  by (oc_eval oc_c30_3174)

lemma oc_c30_3175: "oc_sub oc_b30 3175"
  by (oc_eval oc_c30_3175)

lemma oc_c30_3176: "oc_sub oc_b30 3176"
  by (oc_eval oc_c30_3176)

lemma oc_c30_3177: "oc_sub oc_b30 3177"
  by (oc_eval oc_c30_3177)

lemma oc_c30_3178: "oc_sub oc_b30 3178"
  by (oc_eval oc_c30_3178)

lemma oc_c30_3179: "oc_sub oc_b30 3179"
  by (oc_eval oc_c30_3179)

lemma oc_c30_3180: "oc_sub oc_b30 3180"
  by (oc_eval oc_c30_3180)

lemma oc_c30_3181: "oc_sub oc_b30 3181"
  by (oc_eval oc_c30_3181)

lemma oc_c30_3182: "oc_sub oc_b30 3182"
  by (oc_eval oc_c30_3182)

lemma oc_c30_3183: "oc_sub oc_b30 3183"
  by (oc_eval oc_c30_3183)

lemma upt_c30_198: "[3168..<3184] = [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]"
  by (simp add: upt_rec)

lemma sec_c30_198: "\<forall>j\<in>{16 * 198..<16 * 198 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 198..<16 * 198 + 16}"
  then have "j \<in> set [3168..<3184]" unfolding set_upt by simp
  then have "j \<in> set [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]" unfolding upt_c30_198 .
  then show "oc_sub oc_b30 j" using oc_c30_3168 oc_c30_3169 oc_c30_3170 oc_c30_3171 oc_c30_3172 oc_c30_3173 oc_c30_3174 oc_c30_3175 oc_c30_3176 oc_c30_3177 oc_c30_3178 oc_c30_3179 oc_c30_3180 oc_c30_3181 oc_c30_3182 oc_c30_3183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
