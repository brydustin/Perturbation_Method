theory OCX_c30_190
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3040: "oc_sub oc_b30 3040"
  by (oc_eval oc_c30_3040)

lemma oc_c30_3041: "oc_sub oc_b30 3041"
  by (oc_eval oc_c30_3041)

lemma oc_c30_3042: "oc_sub oc_b30 3042"
  by (oc_eval oc_c30_3042)

lemma oc_c30_3043: "oc_sub oc_b30 3043"
  by (oc_eval oc_c30_3043)

lemma oc_c30_3044: "oc_sub oc_b30 3044"
  by (oc_eval oc_c30_3044)

lemma oc_c30_3045: "oc_sub oc_b30 3045"
  by (oc_eval oc_c30_3045)

lemma oc_c30_3046: "oc_sub oc_b30 3046"
  by (oc_eval oc_c30_3046)

lemma oc_c30_3047: "oc_sub oc_b30 3047"
  by (oc_eval oc_c30_3047)

lemma oc_c30_3048: "oc_sub oc_b30 3048"
  by (oc_eval oc_c30_3048)

lemma oc_c30_3049: "oc_sub oc_b30 3049"
  by (oc_eval oc_c30_3049)

lemma oc_c30_3050: "oc_sub oc_b30 3050"
  by (oc_eval oc_c30_3050)

lemma oc_c30_3051: "oc_sub oc_b30 3051"
  by (oc_eval oc_c30_3051)

lemma oc_c30_3052: "oc_sub oc_b30 3052"
  by (oc_eval oc_c30_3052)

lemma oc_c30_3053: "oc_sub oc_b30 3053"
  by (oc_eval oc_c30_3053)

lemma oc_c30_3054: "oc_sub oc_b30 3054"
  by (oc_eval oc_c30_3054)

lemma oc_c30_3055: "oc_sub oc_b30 3055"
  by (oc_eval oc_c30_3055)

lemma upt_c30_190: "[3040..<3056] = [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]"
  by (simp add: upt_rec)

lemma sec_c30_190: "\<forall>j\<in>{16 * 190..<16 * 190 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 190..<16 * 190 + 16}"
  then have "j \<in> set [3040..<3056]" unfolding set_upt by simp
  then have "j \<in> set [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]" unfolding upt_c30_190 .
  then show "oc_sub oc_b30 j" using oc_c30_3040 oc_c30_3041 oc_c30_3042 oc_c30_3043 oc_c30_3044 oc_c30_3045 oc_c30_3046 oc_c30_3047 oc_c30_3048 oc_c30_3049 oc_c30_3050 oc_c30_3051 oc_c30_3052 oc_c30_3053 oc_c30_3054 oc_c30_3055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
