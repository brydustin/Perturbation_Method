theory DCX_c30_197
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3152: "dc_sub dc_b30 3152"
  by (dc_eval dc_c30_3152)

lemma dc_c30_3153: "dc_sub dc_b30 3153"
  by (dc_eval dc_c30_3153)

lemma dc_c30_3154: "dc_sub dc_b30 3154"
  by (dc_eval dc_c30_3154)

lemma dc_c30_3155: "dc_sub dc_b30 3155"
  by (dc_eval dc_c30_3155)

lemma dc_c30_3156: "dc_sub dc_b30 3156"
  by (dc_eval dc_c30_3156)

lemma dc_c30_3157: "dc_sub dc_b30 3157"
  by (dc_eval dc_c30_3157)

lemma dc_c30_3158: "dc_sub dc_b30 3158"
  by (dc_eval dc_c30_3158)

lemma dc_c30_3159: "dc_sub dc_b30 3159"
  by (dc_eval dc_c30_3159)

lemma dc_c30_3160: "dc_sub dc_b30 3160"
  by (dc_eval dc_c30_3160)

lemma dc_c30_3161: "dc_sub dc_b30 3161"
  by (dc_eval dc_c30_3161)

lemma dc_c30_3162: "dc_sub dc_b30 3162"
  by (dc_eval dc_c30_3162)

lemma dc_c30_3163: "dc_sub dc_b30 3163"
  by (dc_eval dc_c30_3163)

lemma dc_c30_3164: "dc_sub dc_b30 3164"
  by (dc_eval dc_c30_3164)

lemma dc_c30_3165: "dc_sub dc_b30 3165"
  by (dc_eval dc_c30_3165)

lemma dc_c30_3166: "dc_sub dc_b30 3166"
  by (dc_eval dc_c30_3166)

lemma dc_c30_3167: "dc_sub dc_b30 3167"
  by (dc_eval dc_c30_3167)

lemma upt_c30_197: "[3152..<3168] = [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]"
  by (simp add: upt_rec)

lemma sec_c30_197: "\<forall>j\<in>{16 * 197..<16 * 197 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 197..<16 * 197 + 16}"
  then have "j \<in> set [3152..<3168]" unfolding set_upt by simp
  then have "j \<in> set [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]" unfolding upt_c30_197 .
  then show "dc_sub dc_b30 j" using dc_c30_3152 dc_c30_3153 dc_c30_3154 dc_c30_3155 dc_c30_3156 dc_c30_3157 dc_c30_3158 dc_c30_3159 dc_c30_3160 dc_c30_3161 dc_c30_3162 dc_c30_3163 dc_c30_3164 dc_c30_3165 dc_c30_3166 dc_c30_3167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
