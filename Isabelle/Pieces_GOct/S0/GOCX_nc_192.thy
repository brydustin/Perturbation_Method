theory GOCX_nc_192
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3072: "goc_sub None 3072"
  by (goc_eval goc_nc_3072)

lemma goc_nc_3073: "goc_sub None 3073"
  by (goc_eval goc_nc_3073)

lemma goc_nc_3074: "goc_sub None 3074"
  by (goc_eval goc_nc_3074)

lemma goc_nc_3075: "goc_sub None 3075"
  by (goc_eval goc_nc_3075)

lemma goc_nc_3076: "goc_sub None 3076"
  by (goc_eval goc_nc_3076)

lemma goc_nc_3077: "goc_sub None 3077"
  by (goc_eval goc_nc_3077)

lemma goc_nc_3078: "goc_sub None 3078"
  by (goc_eval goc_nc_3078)

lemma goc_nc_3079: "goc_sub None 3079"
  by (goc_eval goc_nc_3079)

lemma goc_nc_3080: "goc_sub None 3080"
  by (goc_eval goc_nc_3080)

lemma goc_nc_3081: "goc_sub None 3081"
  by (goc_eval goc_nc_3081)

lemma goc_nc_3082: "goc_sub None 3082"
  by (goc_eval goc_nc_3082)

lemma goc_nc_3083: "goc_sub None 3083"
  by (goc_eval goc_nc_3083)

lemma goc_nc_3084: "goc_sub None 3084"
  by (goc_eval goc_nc_3084)

lemma goc_nc_3085: "goc_sub None 3085"
  by (goc_eval goc_nc_3085)

lemma goc_nc_3086: "goc_sub None 3086"
  by (goc_eval goc_nc_3086)

lemma goc_nc_3087: "goc_sub None 3087"
  by (goc_eval goc_nc_3087)

lemma gupt_nc_192: "[3072..<3088] = [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]"
  by (simp add: upt_rec)

lemma gsec_nc_192: "\<forall>j\<in>{16 * 192..<16 * 192 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 192..<16 * 192 + 16}"
  then have "j \<in> set [3072..<3088]" unfolding set_upt by simp
  then have "j \<in> set [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]" unfolding gupt_nc_192 .
  then show "goc_sub None j" using goc_nc_3072 goc_nc_3073 goc_nc_3074 goc_nc_3075 goc_nc_3076 goc_nc_3077 goc_nc_3078 goc_nc_3079 goc_nc_3080 goc_nc_3081 goc_nc_3082 goc_nc_3083 goc_nc_3084 goc_nc_3085 goc_nc_3086 goc_nc_3087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
