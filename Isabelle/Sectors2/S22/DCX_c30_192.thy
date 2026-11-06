theory DCX_c30_192
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3072: "dc_sub dc_b30 3072"
  by (dc_eval dc_c30_3072)

lemma dc_c30_3073: "dc_sub dc_b30 3073"
  by (dc_eval dc_c30_3073)

lemma dc_c30_3074: "dc_sub dc_b30 3074"
  by (dc_eval dc_c30_3074)

lemma dc_c30_3075: "dc_sub dc_b30 3075"
  by (dc_eval dc_c30_3075)

lemma dc_c30_3076: "dc_sub dc_b30 3076"
  by (dc_eval dc_c30_3076)

lemma dc_c30_3077: "dc_sub dc_b30 3077"
  by (dc_eval dc_c30_3077)

lemma dc_c30_3078: "dc_sub dc_b30 3078"
  by (dc_eval dc_c30_3078)

lemma dc_c30_3079: "dc_sub dc_b30 3079"
  by (dc_eval dc_c30_3079)

lemma dc_c30_3080: "dc_sub dc_b30 3080"
  by (dc_eval dc_c30_3080)

lemma dc_c30_3081: "dc_sub dc_b30 3081"
  by (dc_eval dc_c30_3081)

lemma dc_c30_3082: "dc_sub dc_b30 3082"
  by (dc_eval dc_c30_3082)

lemma dc_c30_3083: "dc_sub dc_b30 3083"
  by (dc_eval dc_c30_3083)

lemma dc_c30_3084: "dc_sub dc_b30 3084"
  by (dc_eval dc_c30_3084)

lemma dc_c30_3085: "dc_sub dc_b30 3085"
  by (dc_eval dc_c30_3085)

lemma dc_c30_3086: "dc_sub dc_b30 3086"
  by (dc_eval dc_c30_3086)

lemma dc_c30_3087: "dc_sub dc_b30 3087"
  by (dc_eval dc_c30_3087)

lemma upt_c30_192: "[3072..<3088] = [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]"
  by (simp add: upt_rec)

lemma sec_c30_192: "\<forall>j\<in>{16 * 192..<16 * 192 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 192..<16 * 192 + 16}"
  then have "j \<in> set [3072..<3088]" unfolding set_upt by simp
  then have "j \<in> set [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]" unfolding upt_c30_192 .
  then show "dc_sub dc_b30 j" using dc_c30_3072 dc_c30_3073 dc_c30_3074 dc_c30_3075 dc_c30_3076 dc_c30_3077 dc_c30_3078 dc_c30_3079 dc_c30_3080 dc_c30_3081 dc_c30_3082 dc_c30_3083 dc_c30_3084 dc_c30_3085 dc_c30_3086 dc_c30_3087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
