theory GDCX_nc_192
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3072: "gdc_sub None 3072"
  by (gdc_eval gdc_nc_3072)

lemma gdc_nc_3073: "gdc_sub None 3073"
  by (gdc_eval gdc_nc_3073)

lemma gdc_nc_3074: "gdc_sub None 3074"
  by (gdc_eval gdc_nc_3074)

lemma gdc_nc_3075: "gdc_sub None 3075"
  by (gdc_eval gdc_nc_3075)

lemma gdc_nc_3076: "gdc_sub None 3076"
  by (gdc_eval gdc_nc_3076)

lemma gdc_nc_3077: "gdc_sub None 3077"
  by (gdc_eval gdc_nc_3077)

lemma gdc_nc_3078: "gdc_sub None 3078"
  by (gdc_eval gdc_nc_3078)

lemma gdc_nc_3079: "gdc_sub None 3079"
  by (gdc_eval gdc_nc_3079)

lemma gdc_nc_3080: "gdc_sub None 3080"
  by (gdc_eval gdc_nc_3080)

lemma gdc_nc_3081: "gdc_sub None 3081"
  by (gdc_eval gdc_nc_3081)

lemma gdc_nc_3082: "gdc_sub None 3082"
  by (gdc_eval gdc_nc_3082)

lemma gdc_nc_3083: "gdc_sub None 3083"
  by (gdc_eval gdc_nc_3083)

lemma gdc_nc_3084: "gdc_sub None 3084"
  by (gdc_eval gdc_nc_3084)

lemma gdc_nc_3085: "gdc_sub None 3085"
  by (gdc_eval gdc_nc_3085)

lemma gdc_nc_3086: "gdc_sub None 3086"
  by (gdc_eval gdc_nc_3086)

lemma gdc_nc_3087: "gdc_sub None 3087"
  by (gdc_eval gdc_nc_3087)

lemma gupt_nc_192: "[3072..<3088] = [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]"
  by (simp add: upt_rec)

lemma gsec_nc_192: "\<forall>j\<in>{16 * 192..<16 * 192 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 192..<16 * 192 + 16}"
  then have "j \<in> set [3072..<3088]" unfolding set_upt by simp
  then have "j \<in> set [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]" unfolding gupt_nc_192 .
  then show "gdc_sub None j" using gdc_nc_3072 gdc_nc_3073 gdc_nc_3074 gdc_nc_3075 gdc_nc_3076 gdc_nc_3077 gdc_nc_3078 gdc_nc_3079 gdc_nc_3080 gdc_nc_3081 gdc_nc_3082 gdc_nc_3083 gdc_nc_3084 gdc_nc_3085 gdc_nc_3086 gdc_nc_3087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
