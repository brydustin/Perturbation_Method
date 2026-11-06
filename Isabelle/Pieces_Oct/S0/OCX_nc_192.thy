theory OCX_nc_192
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3072: "oc_sub None 3072"
  by (oc_eval oc_nc_3072)

lemma oc_nc_3073: "oc_sub None 3073"
  by (oc_eval oc_nc_3073)

lemma oc_nc_3074: "oc_sub None 3074"
  by (oc_eval oc_nc_3074)

lemma oc_nc_3075: "oc_sub None 3075"
  by (oc_eval oc_nc_3075)

lemma oc_nc_3076: "oc_sub None 3076"
  by (oc_eval oc_nc_3076)

lemma oc_nc_3077: "oc_sub None 3077"
  by (oc_eval oc_nc_3077)

lemma oc_nc_3078: "oc_sub None 3078"
  by (oc_eval oc_nc_3078)

lemma oc_nc_3079: "oc_sub None 3079"
  by (oc_eval oc_nc_3079)

lemma oc_nc_3080: "oc_sub None 3080"
  by (oc_eval oc_nc_3080)

lemma oc_nc_3081: "oc_sub None 3081"
  by (oc_eval oc_nc_3081)

lemma oc_nc_3082: "oc_sub None 3082"
  by (oc_eval oc_nc_3082)

lemma oc_nc_3083: "oc_sub None 3083"
  by (oc_eval oc_nc_3083)

lemma oc_nc_3084: "oc_sub None 3084"
  by (oc_eval oc_nc_3084)

lemma oc_nc_3085: "oc_sub None 3085"
  by (oc_eval oc_nc_3085)

lemma oc_nc_3086: "oc_sub None 3086"
  by (oc_eval oc_nc_3086)

lemma oc_nc_3087: "oc_sub None 3087"
  by (oc_eval oc_nc_3087)

lemma upt_nc_192: "[3072..<3088] = [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]"
  by (simp add: upt_rec)

lemma sec_nc_192: "\<forall>j\<in>{16 * 192..<16 * 192 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 192..<16 * 192 + 16}"
  then have "j \<in> set [3072..<3088]" unfolding set_upt by simp
  then have "j \<in> set [3072, 3073, 3074, 3075, 3076, 3077, 3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087]" unfolding upt_nc_192 .
  then show "oc_sub None j" using oc_nc_3072 oc_nc_3073 oc_nc_3074 oc_nc_3075 oc_nc_3076 oc_nc_3077 oc_nc_3078 oc_nc_3079 oc_nc_3080 oc_nc_3081 oc_nc_3082 oc_nc_3083 oc_nc_3084 oc_nc_3085 oc_nc_3086 oc_nc_3087
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
