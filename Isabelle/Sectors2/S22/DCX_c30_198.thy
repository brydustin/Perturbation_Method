theory DCX_c30_198
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3168: "dc_sub dc_b30 3168"
  by (dc_eval dc_c30_3168)

lemma dc_c30_3169: "dc_sub dc_b30 3169"
  by (dc_eval dc_c30_3169)

lemma dc_c30_3170: "dc_sub dc_b30 3170"
  by (dc_eval dc_c30_3170)

lemma dc_c30_3171: "dc_sub dc_b30 3171"
  by (dc_eval dc_c30_3171)

lemma dc_c30_3172: "dc_sub dc_b30 3172"
  by (dc_eval dc_c30_3172)

lemma dc_c30_3173: "dc_sub dc_b30 3173"
  by (dc_eval dc_c30_3173)

lemma dc_c30_3174: "dc_sub dc_b30 3174"
  by (dc_eval dc_c30_3174)

lemma dc_c30_3175: "dc_sub dc_b30 3175"
  by (dc_eval dc_c30_3175)

lemma dc_c30_3176: "dc_sub dc_b30 3176"
  by (dc_eval dc_c30_3176)

lemma dc_c30_3177: "dc_sub dc_b30 3177"
  by (dc_eval dc_c30_3177)

lemma dc_c30_3178: "dc_sub dc_b30 3178"
  by (dc_eval dc_c30_3178)

lemma dc_c30_3179: "dc_sub dc_b30 3179"
  by (dc_eval dc_c30_3179)

lemma dc_c30_3180: "dc_sub dc_b30 3180"
  by (dc_eval dc_c30_3180)

lemma dc_c30_3181: "dc_sub dc_b30 3181"
  by (dc_eval dc_c30_3181)

lemma dc_c30_3182: "dc_sub dc_b30 3182"
  by (dc_eval dc_c30_3182)

lemma dc_c30_3183: "dc_sub dc_b30 3183"
  by (dc_eval dc_c30_3183)

lemma upt_c30_198: "[3168..<3184] = [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]"
  by (simp add: upt_rec)

lemma sec_c30_198: "\<forall>j\<in>{16 * 198..<16 * 198 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 198..<16 * 198 + 16}"
  then have "j \<in> set [3168..<3184]" unfolding set_upt by simp
  then have "j \<in> set [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]" unfolding upt_c30_198 .
  then show "dc_sub dc_b30 j" using dc_c30_3168 dc_c30_3169 dc_c30_3170 dc_c30_3171 dc_c30_3172 dc_c30_3173 dc_c30_3174 dc_c30_3175 dc_c30_3176 dc_c30_3177 dc_c30_3178 dc_c30_3179 dc_c30_3180 dc_c30_3181 dc_c30_3182 dc_c30_3183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
