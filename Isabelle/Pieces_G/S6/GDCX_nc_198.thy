theory GDCX_nc_198
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3168: "gdc_sub None 3168"
  by (gdc_eval gdc_nc_3168)

lemma gdc_nc_3169: "gdc_sub None 3169"
  by (gdc_eval gdc_nc_3169)

lemma gdc_nc_3170: "gdc_sub None 3170"
  by (gdc_eval gdc_nc_3170)

lemma gdc_nc_3171: "gdc_sub None 3171"
  by (gdc_eval gdc_nc_3171)

lemma gdc_nc_3172: "gdc_sub None 3172"
  by (gdc_eval gdc_nc_3172)

lemma gdc_nc_3173: "gdc_sub None 3173"
  by (gdc_eval gdc_nc_3173)

lemma gdc_nc_3174: "gdc_sub None 3174"
  by (gdc_eval gdc_nc_3174)

lemma gdc_nc_3175: "gdc_sub None 3175"
  by (gdc_eval gdc_nc_3175)

lemma gdc_nc_3176: "gdc_sub None 3176"
  by (gdc_eval gdc_nc_3176)

lemma gdc_nc_3177: "gdc_sub None 3177"
  by (gdc_eval gdc_nc_3177)

lemma gdc_nc_3178: "gdc_sub None 3178"
  by (gdc_eval gdc_nc_3178)

lemma gdc_nc_3179: "gdc_sub None 3179"
  by (gdc_eval gdc_nc_3179)

lemma gdc_nc_3180: "gdc_sub None 3180"
  by (gdc_eval gdc_nc_3180)

lemma gdc_nc_3181: "gdc_sub None 3181"
  by (gdc_eval gdc_nc_3181)

lemma gdc_nc_3182: "gdc_sub None 3182"
  by (gdc_eval gdc_nc_3182)

lemma gdc_nc_3183: "gdc_sub None 3183"
  by (gdc_eval gdc_nc_3183)

lemma gupt_nc_198: "[3168..<3184] = [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]"
  by (simp add: upt_rec)

lemma gsec_nc_198: "\<forall>j\<in>{16 * 198..<16 * 198 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 198..<16 * 198 + 16}"
  then have "j \<in> set [3168..<3184]" unfolding set_upt by simp
  then have "j \<in> set [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]" unfolding gupt_nc_198 .
  then show "gdc_sub None j" using gdc_nc_3168 gdc_nc_3169 gdc_nc_3170 gdc_nc_3171 gdc_nc_3172 gdc_nc_3173 gdc_nc_3174 gdc_nc_3175 gdc_nc_3176 gdc_nc_3177 gdc_nc_3178 gdc_nc_3179 gdc_nc_3180 gdc_nc_3181 gdc_nc_3182 gdc_nc_3183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
