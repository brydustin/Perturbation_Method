theory GDCX_nc_191
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3056: "gdc_sub None 3056"
  by (gdc_eval gdc_nc_3056)

lemma gdc_nc_3057: "gdc_sub None 3057"
  by (gdc_eval gdc_nc_3057)

lemma gdc_nc_3058: "gdc_sub None 3058"
  by (gdc_eval gdc_nc_3058)

lemma gdc_nc_3059: "gdc_sub None 3059"
  by (gdc_eval gdc_nc_3059)

lemma gdc_nc_3060: "gdc_sub None 3060"
  by (gdc_eval gdc_nc_3060)

lemma gdc_nc_3061: "gdc_sub None 3061"
  by (gdc_eval gdc_nc_3061)

lemma gdc_nc_3062: "gdc_sub None 3062"
  by (gdc_eval gdc_nc_3062)

lemma gdc_nc_3063: "gdc_sub None 3063"
  by (gdc_eval gdc_nc_3063)

lemma gdc_nc_3064: "gdc_sub None 3064"
  by (gdc_eval gdc_nc_3064)

lemma gdc_nc_3065: "gdc_sub None 3065"
  by (gdc_eval gdc_nc_3065)

lemma gdc_nc_3066: "gdc_sub None 3066"
  by (gdc_eval gdc_nc_3066)

lemma gdc_nc_3067: "gdc_sub None 3067"
  by (gdc_eval gdc_nc_3067)

lemma gdc_nc_3068: "gdc_sub None 3068"
  by (gdc_eval gdc_nc_3068)

lemma gdc_nc_3069: "gdc_sub None 3069"
  by (gdc_eval gdc_nc_3069)

lemma gdc_nc_3070: "gdc_sub None 3070"
  by (gdc_eval gdc_nc_3070)

lemma gdc_nc_3071: "gdc_sub None 3071"
  by (gdc_eval gdc_nc_3071)

lemma gupt_nc_191: "[3056..<3072] = [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]"
  by (simp add: upt_rec)

lemma gsec_nc_191: "\<forall>j\<in>{16 * 191..<16 * 191 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 191..<16 * 191 + 16}"
  then have "j \<in> set [3056..<3072]" unfolding set_upt by simp
  then have "j \<in> set [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]" unfolding gupt_nc_191 .
  then show "gdc_sub None j" using gdc_nc_3056 gdc_nc_3057 gdc_nc_3058 gdc_nc_3059 gdc_nc_3060 gdc_nc_3061 gdc_nc_3062 gdc_nc_3063 gdc_nc_3064 gdc_nc_3065 gdc_nc_3066 gdc_nc_3067 gdc_nc_3068 gdc_nc_3069 gdc_nc_3070 gdc_nc_3071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
