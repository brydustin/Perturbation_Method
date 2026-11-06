theory OCX_c30_197
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3152: "oc_sub oc_b30 3152"
  by (oc_eval oc_c30_3152)

lemma oc_c30_3153: "oc_sub oc_b30 3153"
  by (oc_eval oc_c30_3153)

lemma oc_c30_3154: "oc_sub oc_b30 3154"
  by (oc_eval oc_c30_3154)

lemma oc_c30_3155: "oc_sub oc_b30 3155"
  by (oc_eval oc_c30_3155)

lemma oc_c30_3156: "oc_sub oc_b30 3156"
  by (oc_eval oc_c30_3156)

lemma oc_c30_3157: "oc_sub oc_b30 3157"
  by (oc_eval oc_c30_3157)

lemma oc_c30_3158: "oc_sub oc_b30 3158"
  by (oc_eval oc_c30_3158)

lemma oc_c30_3159: "oc_sub oc_b30 3159"
  by (oc_eval oc_c30_3159)

lemma oc_c30_3160: "oc_sub oc_b30 3160"
  by (oc_eval oc_c30_3160)

lemma oc_c30_3161: "oc_sub oc_b30 3161"
  by (oc_eval oc_c30_3161)

lemma oc_c30_3162: "oc_sub oc_b30 3162"
  by (oc_eval oc_c30_3162)

lemma oc_c30_3163: "oc_sub oc_b30 3163"
  by (oc_eval oc_c30_3163)

lemma oc_c30_3164: "oc_sub oc_b30 3164"
  by (oc_eval oc_c30_3164)

lemma oc_c30_3165: "oc_sub oc_b30 3165"
  by (oc_eval oc_c30_3165)

lemma oc_c30_3166: "oc_sub oc_b30 3166"
  by (oc_eval oc_c30_3166)

lemma oc_c30_3167: "oc_sub oc_b30 3167"
  by (oc_eval oc_c30_3167)

lemma upt_c30_197: "[3152..<3168] = [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]"
  by (simp add: upt_rec)

lemma sec_c30_197: "\<forall>j\<in>{16 * 197..<16 * 197 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 197..<16 * 197 + 16}"
  then have "j \<in> set [3152..<3168]" unfolding set_upt by simp
  then have "j \<in> set [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]" unfolding upt_c30_197 .
  then show "oc_sub oc_b30 j" using oc_c30_3152 oc_c30_3153 oc_c30_3154 oc_c30_3155 oc_c30_3156 oc_c30_3157 oc_c30_3158 oc_c30_3159 oc_c30_3160 oc_c30_3161 oc_c30_3162 oc_c30_3163 oc_c30_3164 oc_c30_3165 oc_c30_3166 oc_c30_3167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
