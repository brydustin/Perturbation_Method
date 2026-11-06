theory OCX_nc_191
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3056: "oc_sub None 3056"
  by (oc_eval oc_nc_3056)

lemma oc_nc_3057: "oc_sub None 3057"
  by (oc_eval oc_nc_3057)

lemma oc_nc_3058: "oc_sub None 3058"
  by (oc_eval oc_nc_3058)

lemma oc_nc_3059: "oc_sub None 3059"
  by (oc_eval oc_nc_3059)

lemma oc_nc_3060: "oc_sub None 3060"
  by (oc_eval oc_nc_3060)

lemma oc_nc_3061: "oc_sub None 3061"
  by (oc_eval oc_nc_3061)

lemma oc_nc_3062: "oc_sub None 3062"
  by (oc_eval oc_nc_3062)

lemma oc_nc_3063: "oc_sub None 3063"
  by (oc_eval oc_nc_3063)

lemma oc_nc_3064: "oc_sub None 3064"
  by (oc_eval oc_nc_3064)

lemma oc_nc_3065: "oc_sub None 3065"
  by (oc_eval oc_nc_3065)

lemma oc_nc_3066: "oc_sub None 3066"
  by (oc_eval oc_nc_3066)

lemma oc_nc_3067: "oc_sub None 3067"
  by (oc_eval oc_nc_3067)

lemma oc_nc_3068: "oc_sub None 3068"
  by (oc_eval oc_nc_3068)

lemma oc_nc_3069: "oc_sub None 3069"
  by (oc_eval oc_nc_3069)

lemma oc_nc_3070: "oc_sub None 3070"
  by (oc_eval oc_nc_3070)

lemma oc_nc_3071: "oc_sub None 3071"
  by (oc_eval oc_nc_3071)

lemma upt_nc_191: "[3056..<3072] = [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]"
  by (simp add: upt_rec)

lemma sec_nc_191: "\<forall>j\<in>{16 * 191..<16 * 191 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 191..<16 * 191 + 16}"
  then have "j \<in> set [3056..<3072]" unfolding set_upt by simp
  then have "j \<in> set [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]" unfolding upt_nc_191 .
  then show "oc_sub None j" using oc_nc_3056 oc_nc_3057 oc_nc_3058 oc_nc_3059 oc_nc_3060 oc_nc_3061 oc_nc_3062 oc_nc_3063 oc_nc_3064 oc_nc_3065 oc_nc_3066 oc_nc_3067 oc_nc_3068 oc_nc_3069 oc_nc_3070 oc_nc_3071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
