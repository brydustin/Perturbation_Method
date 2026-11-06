theory OCX_nc_195
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3120: "oc_sub None 3120"
  by (oc_eval oc_nc_3120)

lemma oc_nc_3121: "oc_sub None 3121"
  by (oc_eval oc_nc_3121)

lemma oc_nc_3122: "oc_sub None 3122"
  by (oc_eval oc_nc_3122)

lemma oc_nc_3123: "oc_sub None 3123"
  by (oc_eval oc_nc_3123)

lemma oc_nc_3124: "oc_sub None 3124"
  by (oc_eval oc_nc_3124)

lemma oc_nc_3125: "oc_sub None 3125"
  by (oc_eval oc_nc_3125)

lemma oc_nc_3126: "oc_sub None 3126"
  by (oc_eval oc_nc_3126)

lemma oc_nc_3127: "oc_sub None 3127"
  by (oc_eval oc_nc_3127)

lemma oc_nc_3128: "oc_sub None 3128"
  by (oc_eval oc_nc_3128)

lemma oc_nc_3129: "oc_sub None 3129"
  by (oc_eval oc_nc_3129)

lemma oc_nc_3130: "oc_sub None 3130"
  by (oc_eval oc_nc_3130)

lemma oc_nc_3131: "oc_sub None 3131"
  by (oc_eval oc_nc_3131)

lemma oc_nc_3132: "oc_sub None 3132"
  by (oc_eval oc_nc_3132)

lemma oc_nc_3133: "oc_sub None 3133"
  by (oc_eval oc_nc_3133)

lemma oc_nc_3134: "oc_sub None 3134"
  by (oc_eval oc_nc_3134)

lemma oc_nc_3135: "oc_sub None 3135"
  by (oc_eval oc_nc_3135)

lemma upt_nc_195: "[3120..<3136] = [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]"
  by (simp add: upt_rec)

lemma sec_nc_195: "\<forall>j\<in>{16 * 195..<16 * 195 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 195..<16 * 195 + 16}"
  then have "j \<in> set [3120..<3136]" unfolding set_upt by simp
  then have "j \<in> set [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]" unfolding upt_nc_195 .
  then show "oc_sub None j" using oc_nc_3120 oc_nc_3121 oc_nc_3122 oc_nc_3123 oc_nc_3124 oc_nc_3125 oc_nc_3126 oc_nc_3127 oc_nc_3128 oc_nc_3129 oc_nc_3130 oc_nc_3131 oc_nc_3132 oc_nc_3133 oc_nc_3134 oc_nc_3135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
