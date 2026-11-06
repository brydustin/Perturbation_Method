theory DCX_nc_198
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3168: "dc_sub None 3168"
  by (dc_eval dc_nc_3168)

lemma dc_nc_3169: "dc_sub None 3169"
  by (dc_eval dc_nc_3169)

lemma dc_nc_3170: "dc_sub None 3170"
  by (dc_eval dc_nc_3170)

lemma dc_nc_3171: "dc_sub None 3171"
  by (dc_eval dc_nc_3171)

lemma dc_nc_3172: "dc_sub None 3172"
  by (dc_eval dc_nc_3172)

lemma dc_nc_3173: "dc_sub None 3173"
  by (dc_eval dc_nc_3173)

lemma dc_nc_3174: "dc_sub None 3174"
  by (dc_eval dc_nc_3174)

lemma dc_nc_3175: "dc_sub None 3175"
  by (dc_eval dc_nc_3175)

lemma dc_nc_3176: "dc_sub None 3176"
  by (dc_eval dc_nc_3176)

lemma dc_nc_3177: "dc_sub None 3177"
  by (dc_eval dc_nc_3177)

lemma dc_nc_3178: "dc_sub None 3178"
  by (dc_eval dc_nc_3178)

lemma dc_nc_3179: "dc_sub None 3179"
  by (dc_eval dc_nc_3179)

lemma dc_nc_3180: "dc_sub None 3180"
  by (dc_eval dc_nc_3180)

lemma dc_nc_3181: "dc_sub None 3181"
  by (dc_eval dc_nc_3181)

lemma dc_nc_3182: "dc_sub None 3182"
  by (dc_eval dc_nc_3182)

lemma dc_nc_3183: "dc_sub None 3183"
  by (dc_eval dc_nc_3183)

lemma upt_nc_198: "[3168..<3184] = [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]"
  by (simp add: upt_rec)

lemma sec_nc_198: "\<forall>j\<in>{16 * 198..<16 * 198 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 198..<16 * 198 + 16}"
  then have "j \<in> set [3168..<3184]" unfolding set_upt by simp
  then have "j \<in> set [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]" unfolding upt_nc_198 .
  then show "dc_sub None j" using dc_nc_3168 dc_nc_3169 dc_nc_3170 dc_nc_3171 dc_nc_3172 dc_nc_3173 dc_nc_3174 dc_nc_3175 dc_nc_3176 dc_nc_3177 dc_nc_3178 dc_nc_3179 dc_nc_3180 dc_nc_3181 dc_nc_3182 dc_nc_3183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
