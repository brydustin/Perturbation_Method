theory OCX_c30_012
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0192: "oc_sub oc_b30 192"
  by (oc_eval oc_c30_0192)

lemma oc_c30_0193: "oc_sub oc_b30 193"
  by (oc_eval oc_c30_0193)

lemma oc_c30_0194: "oc_sub oc_b30 194"
  by (oc_eval oc_c30_0194)

lemma oc_c30_0195: "oc_sub oc_b30 195"
  by (oc_eval oc_c30_0195)

lemma oc_c30_0196: "oc_sub oc_b30 196"
  by (oc_eval oc_c30_0196)

lemma oc_c30_0197: "oc_sub oc_b30 197"
  by (oc_eval oc_c30_0197)

lemma oc_c30_0198: "oc_sub oc_b30 198"
  by (oc_eval oc_c30_0198)

lemma oc_c30_0199: "oc_sub oc_b30 199"
  by (oc_eval oc_c30_0199)

lemma oc_c30_0200: "oc_sub oc_b30 200"
  by (oc_eval oc_c30_0200)

lemma oc_c30_0201: "oc_sub oc_b30 201"
  by (oc_eval oc_c30_0201)

lemma oc_c30_0202: "oc_sub oc_b30 202"
  by (oc_eval oc_c30_0202)

lemma oc_c30_0203: "oc_sub oc_b30 203"
  by (oc_eval oc_c30_0203)

lemma oc_c30_0204: "oc_sub oc_b30 204"
  by (oc_eval oc_c30_0204)

lemma oc_c30_0205: "oc_sub oc_b30 205"
  by (oc_eval oc_c30_0205)

lemma oc_c30_0206: "oc_sub oc_b30 206"
  by (oc_eval oc_c30_0206)

lemma oc_c30_0207: "oc_sub oc_b30 207"
  by (oc_eval oc_c30_0207)

lemma upt_c30_012: "[192..<208] = [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]"
  by (simp add: upt_rec)

lemma sec_c30_012: "\<forall>j\<in>{16 * 12..<16 * 12 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 12..<16 * 12 + 16}"
  then have "j \<in> set [192..<208]" unfolding set_upt by simp
  then have "j \<in> set [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]" unfolding upt_c30_012 .
  then show "oc_sub oc_b30 j" using oc_c30_0192 oc_c30_0193 oc_c30_0194 oc_c30_0195 oc_c30_0196 oc_c30_0197 oc_c30_0198 oc_c30_0199 oc_c30_0200 oc_c30_0201 oc_c30_0202 oc_c30_0203 oc_c30_0204 oc_c30_0205 oc_c30_0206 oc_c30_0207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
