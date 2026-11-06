theory DCX_c30_012
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0192: "dc_sub dc_b30 192"
  by (dc_eval dc_c30_0192)

lemma dc_c30_0193: "dc_sub dc_b30 193"
  by (dc_eval dc_c30_0193)

lemma dc_c30_0194: "dc_sub dc_b30 194"
  by (dc_eval dc_c30_0194)

lemma dc_c30_0195: "dc_sub dc_b30 195"
  by (dc_eval dc_c30_0195)

lemma dc_c30_0196: "dc_sub dc_b30 196"
  by (dc_eval dc_c30_0196)

lemma dc_c30_0197: "dc_sub dc_b30 197"
  by (dc_eval dc_c30_0197)

lemma dc_c30_0198: "dc_sub dc_b30 198"
  by (dc_eval dc_c30_0198)

lemma dc_c30_0199: "dc_sub dc_b30 199"
  by (dc_eval dc_c30_0199)

lemma dc_c30_0200: "dc_sub dc_b30 200"
  by (dc_eval dc_c30_0200)

lemma dc_c30_0201: "dc_sub dc_b30 201"
  by (dc_eval dc_c30_0201)

lemma dc_c30_0202: "dc_sub dc_b30 202"
  by (dc_eval dc_c30_0202)

lemma dc_c30_0203: "dc_sub dc_b30 203"
  by (dc_eval dc_c30_0203)

lemma dc_c30_0204: "dc_sub dc_b30 204"
  by (dc_eval dc_c30_0204)

lemma dc_c30_0205: "dc_sub dc_b30 205"
  by (dc_eval dc_c30_0205)

lemma dc_c30_0206: "dc_sub dc_b30 206"
  by (dc_eval dc_c30_0206)

lemma dc_c30_0207: "dc_sub dc_b30 207"
  by (dc_eval dc_c30_0207)

lemma upt_c30_012: "[192..<208] = [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]"
  by (simp add: upt_rec)

lemma sec_c30_012: "\<forall>j\<in>{16 * 12..<16 * 12 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 12..<16 * 12 + 16}"
  then have "j \<in> set [192..<208]" unfolding set_upt by simp
  then have "j \<in> set [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]" unfolding upt_c30_012 .
  then show "dc_sub dc_b30 j" using dc_c30_0192 dc_c30_0193 dc_c30_0194 dc_c30_0195 dc_c30_0196 dc_c30_0197 dc_c30_0198 dc_c30_0199 dc_c30_0200 dc_c30_0201 dc_c30_0202 dc_c30_0203 dc_c30_0204 dc_c30_0205 dc_c30_0206 dc_c30_0207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
