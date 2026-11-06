theory DCX_c30_191
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3056: "dc_sub dc_b30 3056"
  by (dc_eval dc_c30_3056)

lemma dc_c30_3057: "dc_sub dc_b30 3057"
  by (dc_eval dc_c30_3057)

lemma dc_c30_3058: "dc_sub dc_b30 3058"
  by (dc_eval dc_c30_3058)

lemma dc_c30_3059: "dc_sub dc_b30 3059"
  by (dc_eval dc_c30_3059)

lemma dc_c30_3060: "dc_sub dc_b30 3060"
  by (dc_eval dc_c30_3060)

lemma dc_c30_3061: "dc_sub dc_b30 3061"
  by (dc_eval dc_c30_3061)

lemma dc_c30_3062: "dc_sub dc_b30 3062"
  by (dc_eval dc_c30_3062)

lemma dc_c30_3063: "dc_sub dc_b30 3063"
  by (dc_eval dc_c30_3063)

lemma dc_c30_3064: "dc_sub dc_b30 3064"
  by (dc_eval dc_c30_3064)

lemma dc_c30_3065: "dc_sub dc_b30 3065"
  by (dc_eval dc_c30_3065)

lemma dc_c30_3066: "dc_sub dc_b30 3066"
  by (dc_eval dc_c30_3066)

lemma dc_c30_3067: "dc_sub dc_b30 3067"
  by (dc_eval dc_c30_3067)

lemma dc_c30_3068: "dc_sub dc_b30 3068"
  by (dc_eval dc_c30_3068)

lemma dc_c30_3069: "dc_sub dc_b30 3069"
  by (dc_eval dc_c30_3069)

lemma dc_c30_3070: "dc_sub dc_b30 3070"
  by (dc_eval dc_c30_3070)

lemma dc_c30_3071: "dc_sub dc_b30 3071"
  by (dc_eval dc_c30_3071)

lemma upt_c30_191: "[3056..<3072] = [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]"
  by (simp add: upt_rec)

lemma sec_c30_191: "\<forall>j\<in>{16 * 191..<16 * 191 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 191..<16 * 191 + 16}"
  then have "j \<in> set [3056..<3072]" unfolding set_upt by simp
  then have "j \<in> set [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]" unfolding upt_c30_191 .
  then show "dc_sub dc_b30 j" using dc_c30_3056 dc_c30_3057 dc_c30_3058 dc_c30_3059 dc_c30_3060 dc_c30_3061 dc_c30_3062 dc_c30_3063 dc_c30_3064 dc_c30_3065 dc_c30_3066 dc_c30_3067 dc_c30_3068 dc_c30_3069 dc_c30_3070 dc_c30_3071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
