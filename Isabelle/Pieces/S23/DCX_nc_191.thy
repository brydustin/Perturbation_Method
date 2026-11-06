theory DCX_nc_191
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3056: "dc_sub None 3056"
  by (dc_eval dc_nc_3056)

lemma dc_nc_3057: "dc_sub None 3057"
  by (dc_eval dc_nc_3057)

lemma dc_nc_3058: "dc_sub None 3058"
  by (dc_eval dc_nc_3058)

lemma dc_nc_3059: "dc_sub None 3059"
  by (dc_eval dc_nc_3059)

lemma dc_nc_3060: "dc_sub None 3060"
  by (dc_eval dc_nc_3060)

lemma dc_nc_3061: "dc_sub None 3061"
  by (dc_eval dc_nc_3061)

lemma dc_nc_3062: "dc_sub None 3062"
  by (dc_eval dc_nc_3062)

lemma dc_nc_3063: "dc_sub None 3063"
  by (dc_eval dc_nc_3063)

lemma dc_nc_3064: "dc_sub None 3064"
  by (dc_eval dc_nc_3064)

lemma dc_nc_3065: "dc_sub None 3065"
  by (dc_eval dc_nc_3065)

lemma dc_nc_3066: "dc_sub None 3066"
  by (dc_eval dc_nc_3066)

lemma dc_nc_3067: "dc_sub None 3067"
  by (dc_eval dc_nc_3067)

lemma dc_nc_3068: "dc_sub None 3068"
  by (dc_eval dc_nc_3068)

lemma dc_nc_3069: "dc_sub None 3069"
  by (dc_eval dc_nc_3069)

lemma dc_nc_3070: "dc_sub None 3070"
  by (dc_eval dc_nc_3070)

lemma dc_nc_3071: "dc_sub None 3071"
  by (dc_eval dc_nc_3071)

lemma upt_nc_191: "[3056..<3072] = [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]"
  by (simp add: upt_rec)

lemma sec_nc_191: "\<forall>j\<in>{16 * 191..<16 * 191 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 191..<16 * 191 + 16}"
  then have "j \<in> set [3056..<3072]" unfolding set_upt by simp
  then have "j \<in> set [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]" unfolding upt_nc_191 .
  then show "dc_sub None j" using dc_nc_3056 dc_nc_3057 dc_nc_3058 dc_nc_3059 dc_nc_3060 dc_nc_3061 dc_nc_3062 dc_nc_3063 dc_nc_3064 dc_nc_3065 dc_nc_3066 dc_nc_3067 dc_nc_3068 dc_nc_3069 dc_nc_3070 dc_nc_3071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
