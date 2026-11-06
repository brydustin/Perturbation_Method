theory OCX_nc_198
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3168: "oc_sub None 3168"
  by (oc_eval oc_nc_3168)

lemma oc_nc_3169: "oc_sub None 3169"
  by (oc_eval oc_nc_3169)

lemma oc_nc_3170: "oc_sub None 3170"
  by (oc_eval oc_nc_3170)

lemma oc_nc_3171: "oc_sub None 3171"
  by (oc_eval oc_nc_3171)

lemma oc_nc_3172: "oc_sub None 3172"
  by (oc_eval oc_nc_3172)

lemma oc_nc_3173: "oc_sub None 3173"
  by (oc_eval oc_nc_3173)

lemma oc_nc_3174: "oc_sub None 3174"
  by (oc_eval oc_nc_3174)

lemma oc_nc_3175: "oc_sub None 3175"
  by (oc_eval oc_nc_3175)

lemma oc_nc_3176: "oc_sub None 3176"
  by (oc_eval oc_nc_3176)

lemma oc_nc_3177: "oc_sub None 3177"
  by (oc_eval oc_nc_3177)

lemma oc_nc_3178: "oc_sub None 3178"
  by (oc_eval oc_nc_3178)

lemma oc_nc_3179: "oc_sub None 3179"
  by (oc_eval oc_nc_3179)

lemma oc_nc_3180: "oc_sub None 3180"
  by (oc_eval oc_nc_3180)

lemma oc_nc_3181: "oc_sub None 3181"
  by (oc_eval oc_nc_3181)

lemma oc_nc_3182: "oc_sub None 3182"
  by (oc_eval oc_nc_3182)

lemma oc_nc_3183: "oc_sub None 3183"
  by (oc_eval oc_nc_3183)

lemma upt_nc_198: "[3168..<3184] = [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]"
  by (simp add: upt_rec)

lemma sec_nc_198: "\<forall>j\<in>{16 * 198..<16 * 198 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 198..<16 * 198 + 16}"
  then have "j \<in> set [3168..<3184]" unfolding set_upt by simp
  then have "j \<in> set [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]" unfolding upt_nc_198 .
  then show "oc_sub None j" using oc_nc_3168 oc_nc_3169 oc_nc_3170 oc_nc_3171 oc_nc_3172 oc_nc_3173 oc_nc_3174 oc_nc_3175 oc_nc_3176 oc_nc_3177 oc_nc_3178 oc_nc_3179 oc_nc_3180 oc_nc_3181 oc_nc_3182 oc_nc_3183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
