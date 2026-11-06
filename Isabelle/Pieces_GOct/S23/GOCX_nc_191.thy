theory GOCX_nc_191
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3056: "goc_sub None 3056"
  by (goc_eval goc_nc_3056)

lemma goc_nc_3057: "goc_sub None 3057"
  by (goc_eval goc_nc_3057)

lemma goc_nc_3058: "goc_sub None 3058"
  by (goc_eval goc_nc_3058)

lemma goc_nc_3059: "goc_sub None 3059"
  by (goc_eval goc_nc_3059)

lemma goc_nc_3060: "goc_sub None 3060"
  by (goc_eval goc_nc_3060)

lemma goc_nc_3061: "goc_sub None 3061"
  by (goc_eval goc_nc_3061)

lemma goc_nc_3062: "goc_sub None 3062"
  by (goc_eval goc_nc_3062)

lemma goc_nc_3063: "goc_sub None 3063"
  by (goc_eval goc_nc_3063)

lemma goc_nc_3064: "goc_sub None 3064"
  by (goc_eval goc_nc_3064)

lemma goc_nc_3065: "goc_sub None 3065"
  by (goc_eval goc_nc_3065)

lemma goc_nc_3066: "goc_sub None 3066"
  by (goc_eval goc_nc_3066)

lemma goc_nc_3067: "goc_sub None 3067"
  by (goc_eval goc_nc_3067)

lemma goc_nc_3068: "goc_sub None 3068"
  by (goc_eval goc_nc_3068)

lemma goc_nc_3069: "goc_sub None 3069"
  by (goc_eval goc_nc_3069)

lemma goc_nc_3070: "goc_sub None 3070"
  by (goc_eval goc_nc_3070)

lemma goc_nc_3071: "goc_sub None 3071"
  by (goc_eval goc_nc_3071)

lemma gupt_nc_191: "[3056..<3072] = [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]"
  by (simp add: upt_rec)

lemma gsec_nc_191: "\<forall>j\<in>{16 * 191..<16 * 191 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 191..<16 * 191 + 16}"
  then have "j \<in> set [3056..<3072]" unfolding set_upt by simp
  then have "j \<in> set [3056, 3057, 3058, 3059, 3060, 3061, 3062, 3063, 3064, 3065, 3066, 3067, 3068, 3069, 3070, 3071]" unfolding gupt_nc_191 .
  then show "goc_sub None j" using goc_nc_3056 goc_nc_3057 goc_nc_3058 goc_nc_3059 goc_nc_3060 goc_nc_3061 goc_nc_3062 goc_nc_3063 goc_nc_3064 goc_nc_3065 goc_nc_3066 goc_nc_3067 goc_nc_3068 goc_nc_3069 goc_nc_3070 goc_nc_3071
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
