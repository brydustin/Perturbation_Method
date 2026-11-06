theory GOCX_nc_198
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3168: "goc_sub None 3168"
  by (goc_eval goc_nc_3168)

lemma goc_nc_3169: "goc_sub None 3169"
  by (goc_eval goc_nc_3169)

lemma goc_nc_3170: "goc_sub None 3170"
  by (goc_eval goc_nc_3170)

lemma goc_nc_3171: "goc_sub None 3171"
  by (goc_eval goc_nc_3171)

lemma goc_nc_3172: "goc_sub None 3172"
  by (goc_eval goc_nc_3172)

lemma goc_nc_3173: "goc_sub None 3173"
  by (goc_eval goc_nc_3173)

lemma goc_nc_3174: "goc_sub None 3174"
  by (goc_eval goc_nc_3174)

lemma goc_nc_3175: "goc_sub None 3175"
  by (goc_eval goc_nc_3175)

lemma goc_nc_3176: "goc_sub None 3176"
  by (goc_eval goc_nc_3176)

lemma goc_nc_3177: "goc_sub None 3177"
  by (goc_eval goc_nc_3177)

lemma goc_nc_3178: "goc_sub None 3178"
  by (goc_eval goc_nc_3178)

lemma goc_nc_3179: "goc_sub None 3179"
  by (goc_eval goc_nc_3179)

lemma goc_nc_3180: "goc_sub None 3180"
  by (goc_eval goc_nc_3180)

lemma goc_nc_3181: "goc_sub None 3181"
  by (goc_eval goc_nc_3181)

lemma goc_nc_3182: "goc_sub None 3182"
  by (goc_eval goc_nc_3182)

lemma goc_nc_3183: "goc_sub None 3183"
  by (goc_eval goc_nc_3183)

lemma gupt_nc_198: "[3168..<3184] = [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]"
  by (simp add: upt_rec)

lemma gsec_nc_198: "\<forall>j\<in>{16 * 198..<16 * 198 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 198..<16 * 198 + 16}"
  then have "j \<in> set [3168..<3184]" unfolding set_upt by simp
  then have "j \<in> set [3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183]" unfolding gupt_nc_198 .
  then show "goc_sub None j" using goc_nc_3168 goc_nc_3169 goc_nc_3170 goc_nc_3171 goc_nc_3172 goc_nc_3173 goc_nc_3174 goc_nc_3175 goc_nc_3176 goc_nc_3177 goc_nc_3178 goc_nc_3179 goc_nc_3180 goc_nc_3181 goc_nc_3182 goc_nc_3183
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
