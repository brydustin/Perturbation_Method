theory DCX_nc_192
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3072: "dc_sub None 3072"
  by (dc_eval dc_nc_3072)

lemma dc_nc_3073: "dc_sub None 3073"
  by (dc_eval dc_nc_3073)

lemma dc_nc_3074: "dc_sub None 3074"
  by (dc_eval dc_nc_3074)

lemma dc_nc_3075: "dc_sub None 3075"
  by (dc_eval dc_nc_3075)

lemma dc_nc_3076: "dc_sub None 3076"
  by (dc_eval dc_nc_3076)

lemma dc_nc_3077: "dc_sub None 3077"
  by (dc_eval dc_nc_3077)

lemma dc_nc_3078: "dc_sub None 3078"
  by (dc_eval dc_nc_3078)

lemma dc_nc_3079: "dc_sub None 3079"
  by (dc_eval dc_nc_3079)

lemma dc_nc_3080: "dc_sub None 3080"
  by (dc_eval dc_nc_3080)

lemma dc_nc_3081: "dc_sub None 3081"
  by (dc_eval dc_nc_3081)

lemma dc_nc_3082: "dc_sub None 3082"
  by (dc_eval dc_nc_3082)

lemma dc_nc_3083: "dc_sub None 3083"
  by (dc_eval dc_nc_3083)

lemma dc_nc_3084: "dc_sub None 3084"
  by (dc_eval dc_nc_3084)

lemma dc_nc_3085: "dc_sub None 3085"
  by (dc_eval dc_nc_3085)

lemma dc_nc_3086: "dc_sub None 3086"
  by (dc_eval dc_nc_3086)

lemma dc_nc_3087: "dc_sub None 3087"
  by (dc_eval dc_nc_3087)

lemma upt_nc_192: "[3072..<3088] = [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]"
  by (simp add: upt_rec)

lemma sec_nc_192: "\<forall>j\<in>{16 * 192..<16 * 192 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 192..<16 * 192 + 16}"
  then have "j \<in> set [3072..<3088]" unfolding set_upt by simp
  then have "j \<in> set [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]" unfolding upt_nc_192 .
  then show "dc_sub None j" using dc_nc_3072 dc_nc_3073 dc_nc_3074 dc_nc_3075 dc_nc_3076 dc_nc_3077 dc_nc_3078 dc_nc_3079 dc_nc_3080 dc_nc_3081 dc_nc_3082 dc_nc_3083 dc_nc_3084 dc_nc_3085 dc_nc_3086 dc_nc_3087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
