theory OCX_c30_195
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3120: "oc_sub oc_b30 3120"
  by (oc_eval oc_c30_3120)

lemma oc_c30_3121: "oc_sub oc_b30 3121"
  by (oc_eval oc_c30_3121)

lemma oc_c30_3122: "oc_sub oc_b30 3122"
  by (oc_eval oc_c30_3122)

lemma oc_c30_3123: "oc_sub oc_b30 3123"
  by (oc_eval oc_c30_3123)

lemma oc_c30_3124: "oc_sub oc_b30 3124"
  by (oc_eval oc_c30_3124)

lemma oc_c30_3125: "oc_sub oc_b30 3125"
  by (oc_eval oc_c30_3125)

lemma oc_c30_3126: "oc_sub oc_b30 3126"
  by (oc_eval oc_c30_3126)

lemma oc_c30_3127: "oc_sub oc_b30 3127"
  by (oc_eval oc_c30_3127)

lemma oc_c30_3128: "oc_sub oc_b30 3128"
  by (oc_eval oc_c30_3128)

lemma oc_c30_3129: "oc_sub oc_b30 3129"
  by (oc_eval oc_c30_3129)

lemma oc_c30_3130: "oc_sub oc_b30 3130"
  by (oc_eval oc_c30_3130)

lemma oc_c30_3131: "oc_sub oc_b30 3131"
  by (oc_eval oc_c30_3131)

lemma oc_c30_3132: "oc_sub oc_b30 3132"
  by (oc_eval oc_c30_3132)

lemma oc_c30_3133: "oc_sub oc_b30 3133"
  by (oc_eval oc_c30_3133)

lemma oc_c30_3134: "oc_sub oc_b30 3134"
  by (oc_eval oc_c30_3134)

lemma oc_c30_3135: "oc_sub oc_b30 3135"
  by (oc_eval oc_c30_3135)

lemma upt_c30_195: "[3120..<3136] = [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]"
  by (simp add: upt_rec)

lemma sec_c30_195: "\<forall>j\<in>{16 * 195..<16 * 195 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 195..<16 * 195 + 16}"
  then have "j \<in> set [3120..<3136]" unfolding set_upt by simp
  then have "j \<in> set [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]" unfolding upt_c30_195 .
  then show "oc_sub oc_b30 j" using oc_c30_3120 oc_c30_3121 oc_c30_3122 oc_c30_3123 oc_c30_3124 oc_c30_3125 oc_c30_3126 oc_c30_3127 oc_c30_3128 oc_c30_3129 oc_c30_3130 oc_c30_3131 oc_c30_3132 oc_c30_3133 oc_c30_3134 oc_c30_3135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
