theory OCX_c30_200
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3200: "oc_sub oc_b30 3200"
  by (oc_eval oc_c30_3200)

lemma oc_c30_3201: "oc_sub oc_b30 3201"
  by (oc_eval oc_c30_3201)

lemma oc_c30_3202: "oc_sub oc_b30 3202"
  by (oc_eval oc_c30_3202)

lemma oc_c30_3203: "oc_sub oc_b30 3203"
  by (oc_eval oc_c30_3203)

lemma oc_c30_3204: "oc_sub oc_b30 3204"
  by (oc_eval oc_c30_3204)

lemma oc_c30_3205: "oc_sub oc_b30 3205"
  by (oc_eval oc_c30_3205)

lemma oc_c30_3206: "oc_sub oc_b30 3206"
  by (oc_eval oc_c30_3206)

lemma oc_c30_3207: "oc_sub oc_b30 3207"
  by (oc_eval oc_c30_3207)

lemma oc_c30_3208: "oc_sub oc_b30 3208"
  by (oc_eval oc_c30_3208)

lemma oc_c30_3209: "oc_sub oc_b30 3209"
  by (oc_eval oc_c30_3209)

lemma oc_c30_3210: "oc_sub oc_b30 3210"
  by (oc_eval oc_c30_3210)

lemma oc_c30_3211: "oc_sub oc_b30 3211"
  by (oc_eval oc_c30_3211)

lemma oc_c30_3212: "oc_sub oc_b30 3212"
  by (oc_eval oc_c30_3212)

lemma oc_c30_3213: "oc_sub oc_b30 3213"
  by (oc_eval oc_c30_3213)

lemma oc_c30_3214: "oc_sub oc_b30 3214"
  by (oc_eval oc_c30_3214)

lemma oc_c30_3215: "oc_sub oc_b30 3215"
  by (oc_eval oc_c30_3215)

lemma upt_c30_200: "[3200..<3216] = [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]"
  by (simp add: upt_rec)

lemma sec_c30_200: "\<forall>j\<in>{16 * 200..<16 * 200 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 200..<16 * 200 + 16}"
  then have "j \<in> set [3200..<3216]" unfolding set_upt by simp
  then have "j \<in> set [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]" unfolding upt_c30_200 .
  then show "oc_sub oc_b30 j" using oc_c30_3200 oc_c30_3201 oc_c30_3202 oc_c30_3203 oc_c30_3204 oc_c30_3205 oc_c30_3206 oc_c30_3207 oc_c30_3208 oc_c30_3209 oc_c30_3210 oc_c30_3211 oc_c30_3212 oc_c30_3213 oc_c30_3214 oc_c30_3215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
