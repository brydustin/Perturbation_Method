theory DCX_c30_190
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3040: "dc_sub dc_b30 3040"
  by (dc_eval dc_c30_3040)

lemma dc_c30_3041: "dc_sub dc_b30 3041"
  by (dc_eval dc_c30_3041)

lemma dc_c30_3042: "dc_sub dc_b30 3042"
  by (dc_eval dc_c30_3042)

lemma dc_c30_3043: "dc_sub dc_b30 3043"
  by (dc_eval dc_c30_3043)

lemma dc_c30_3044: "dc_sub dc_b30 3044"
  by (dc_eval dc_c30_3044)

lemma dc_c30_3045: "dc_sub dc_b30 3045"
  by (dc_eval dc_c30_3045)

lemma dc_c30_3046: "dc_sub dc_b30 3046"
  by (dc_eval dc_c30_3046)

lemma dc_c30_3047: "dc_sub dc_b30 3047"
  by (dc_eval dc_c30_3047)

lemma dc_c30_3048: "dc_sub dc_b30 3048"
  by (dc_eval dc_c30_3048)

lemma dc_c30_3049: "dc_sub dc_b30 3049"
  by (dc_eval dc_c30_3049)

lemma dc_c30_3050: "dc_sub dc_b30 3050"
  by (dc_eval dc_c30_3050)

lemma dc_c30_3051: "dc_sub dc_b30 3051"
  by (dc_eval dc_c30_3051)

lemma dc_c30_3052: "dc_sub dc_b30 3052"
  by (dc_eval dc_c30_3052)

lemma dc_c30_3053: "dc_sub dc_b30 3053"
  by (dc_eval dc_c30_3053)

lemma dc_c30_3054: "dc_sub dc_b30 3054"
  by (dc_eval dc_c30_3054)

lemma dc_c30_3055: "dc_sub dc_b30 3055"
  by (dc_eval dc_c30_3055)

lemma upt_c30_190: "[3040..<3056] = [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]"
  by (simp add: upt_rec)

lemma sec_c30_190: "\<forall>j\<in>{16 * 190..<16 * 190 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 190..<16 * 190 + 16}"
  then have "j \<in> set [3040..<3056]" unfolding set_upt by simp
  then have "j \<in> set [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]" unfolding upt_c30_190 .
  then show "dc_sub dc_b30 j" using dc_c30_3040 dc_c30_3041 dc_c30_3042 dc_c30_3043 dc_c30_3044 dc_c30_3045 dc_c30_3046 dc_c30_3047 dc_c30_3048 dc_c30_3049 dc_c30_3050 dc_c30_3051 dc_c30_3052 dc_c30_3053 dc_c30_3054 dc_c30_3055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
