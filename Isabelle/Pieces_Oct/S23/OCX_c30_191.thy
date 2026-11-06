theory OCX_c30_191
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3056: "oc_sub oc_b30 3056"
  by (oc_eval oc_c30_3056)

lemma oc_c30_3057: "oc_sub oc_b30 3057"
  by (oc_eval oc_c30_3057)

lemma oc_c30_3058: "oc_sub oc_b30 3058"
  by (oc_eval oc_c30_3058)

lemma oc_c30_3059: "oc_sub oc_b30 3059"
  by (oc_eval oc_c30_3059)

lemma oc_c30_3060: "oc_sub oc_b30 3060"
  by (oc_eval oc_c30_3060)

lemma oc_c30_3061: "oc_sub oc_b30 3061"
  by (oc_eval oc_c30_3061)

lemma oc_c30_3062: "oc_sub oc_b30 3062"
  by (oc_eval oc_c30_3062)

lemma oc_c30_3063: "oc_sub oc_b30 3063"
  by (oc_eval oc_c30_3063)

lemma oc_c30_3064: "oc_sub oc_b30 3064"
  by (oc_eval oc_c30_3064)

lemma oc_c30_3065: "oc_sub oc_b30 3065"
  by (oc_eval oc_c30_3065)

lemma oc_c30_3066: "oc_sub oc_b30 3066"
  by (oc_eval oc_c30_3066)

lemma oc_c30_3067: "oc_sub oc_b30 3067"
  by (oc_eval oc_c30_3067)

lemma oc_c30_3068: "oc_sub oc_b30 3068"
  by (oc_eval oc_c30_3068)

lemma oc_c30_3069: "oc_sub oc_b30 3069"
  by (oc_eval oc_c30_3069)

lemma oc_c30_3070: "oc_sub oc_b30 3070"
  by (oc_eval oc_c30_3070)

lemma oc_c30_3071: "oc_sub oc_b30 3071"
  by (oc_eval oc_c30_3071)

lemma upt_c30_191: "[3056..<3072] = [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]"
  by (simp add: upt_rec)

lemma sec_c30_191: "\<forall>j\<in>{16 * 191..<16 * 191 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 191..<16 * 191 + 16}"
  then have "j \<in> set [3056..<3072]" unfolding set_upt by simp
  then have "j \<in> set [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]" unfolding upt_c30_191 .
  then show "oc_sub oc_b30 j" using oc_c30_3056 oc_c30_3057 oc_c30_3058 oc_c30_3059 oc_c30_3060 oc_c30_3061 oc_c30_3062 oc_c30_3063 oc_c30_3064 oc_c30_3065 oc_c30_3066 oc_c30_3067 oc_c30_3068 oc_c30_3069 oc_c30_3070 oc_c30_3071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
