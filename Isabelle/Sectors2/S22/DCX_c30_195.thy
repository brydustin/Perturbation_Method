theory DCX_c30_195
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3120: "dc_sub dc_b30 3120"
  by (dc_eval dc_c30_3120)

lemma dc_c30_3121: "dc_sub dc_b30 3121"
  by (dc_eval dc_c30_3121)

lemma dc_c30_3122: "dc_sub dc_b30 3122"
  by (dc_eval dc_c30_3122)

lemma dc_c30_3123: "dc_sub dc_b30 3123"
  by (dc_eval dc_c30_3123)

lemma dc_c30_3124: "dc_sub dc_b30 3124"
  by (dc_eval dc_c30_3124)

lemma dc_c30_3125: "dc_sub dc_b30 3125"
  by (dc_eval dc_c30_3125)

lemma dc_c30_3126: "dc_sub dc_b30 3126"
  by (dc_eval dc_c30_3126)

lemma dc_c30_3127: "dc_sub dc_b30 3127"
  by (dc_eval dc_c30_3127)

lemma dc_c30_3128: "dc_sub dc_b30 3128"
  by (dc_eval dc_c30_3128)

lemma dc_c30_3129: "dc_sub dc_b30 3129"
  by (dc_eval dc_c30_3129)

lemma dc_c30_3130: "dc_sub dc_b30 3130"
  by (dc_eval dc_c30_3130)

lemma dc_c30_3131: "dc_sub dc_b30 3131"
  by (dc_eval dc_c30_3131)

lemma dc_c30_3132: "dc_sub dc_b30 3132"
  by (dc_eval dc_c30_3132)

lemma dc_c30_3133: "dc_sub dc_b30 3133"
  by (dc_eval dc_c30_3133)

lemma dc_c30_3134: "dc_sub dc_b30 3134"
  by (dc_eval dc_c30_3134)

lemma dc_c30_3135: "dc_sub dc_b30 3135"
  by (dc_eval dc_c30_3135)

lemma upt_c30_195: "[3120..<3136] = [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]"
  by (simp add: upt_rec)

lemma sec_c30_195: "\<forall>j\<in>{16 * 195..<16 * 195 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 195..<16 * 195 + 16}"
  then have "j \<in> set [3120..<3136]" unfolding set_upt by simp
  then have "j \<in> set [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]" unfolding upt_c30_195 .
  then show "dc_sub dc_b30 j" using dc_c30_3120 dc_c30_3121 dc_c30_3122 dc_c30_3123 dc_c30_3124 dc_c30_3125 dc_c30_3126 dc_c30_3127 dc_c30_3128 dc_c30_3129 dc_c30_3130 dc_c30_3131 dc_c30_3132 dc_c30_3133 dc_c30_3134 dc_c30_3135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
