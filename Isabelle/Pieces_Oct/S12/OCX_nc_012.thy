theory OCX_nc_012
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0192: "oc_sub None 192"
  by (oc_eval oc_nc_0192)

lemma oc_nc_0193: "oc_sub None 193"
  by (oc_eval oc_nc_0193)

lemma oc_nc_0194: "oc_sub None 194"
  by (oc_eval oc_nc_0194)

lemma oc_nc_0195: "oc_sub None 195"
  by (oc_eval oc_nc_0195)

lemma oc_nc_0196: "oc_sub None 196"
  by (oc_eval oc_nc_0196)

lemma oc_nc_0197: "oc_sub None 197"
  by (oc_eval oc_nc_0197)

lemma oc_nc_0198: "oc_sub None 198"
  by (oc_eval oc_nc_0198)

lemma oc_nc_0199: "oc_sub None 199"
  by (oc_eval oc_nc_0199)

lemma oc_nc_0200: "oc_sub None 200"
  by (oc_eval oc_nc_0200)

lemma oc_nc_0201: "oc_sub None 201"
  by (oc_eval oc_nc_0201)

lemma oc_nc_0202: "oc_sub None 202"
  by (oc_eval oc_nc_0202)

lemma oc_nc_0203: "oc_sub None 203"
  by (oc_eval oc_nc_0203)

lemma oc_nc_0204: "oc_sub None 204"
  by (oc_eval oc_nc_0204)

lemma oc_nc_0205: "oc_sub None 205"
  by (oc_eval oc_nc_0205)

lemma oc_nc_0206: "oc_sub None 206"
  by (oc_eval oc_nc_0206)

lemma oc_nc_0207: "oc_sub None 207"
  by (oc_eval oc_nc_0207)

lemma upt_nc_012: "[192..<208] = [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]"
  by (simp add: upt_rec)

lemma sec_nc_012: "\<forall>j\<in>{16 * 12..<16 * 12 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 12..<16 * 12 + 16}"
  then have "j \<in> set [192..<208]" unfolding set_upt by simp
  then have "j \<in> set [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]" unfolding upt_nc_012 .
  then show "oc_sub None j" using oc_nc_0192 oc_nc_0193 oc_nc_0194 oc_nc_0195 oc_nc_0196 oc_nc_0197 oc_nc_0198 oc_nc_0199 oc_nc_0200 oc_nc_0201 oc_nc_0202 oc_nc_0203 oc_nc_0204 oc_nc_0205 oc_nc_0206 oc_nc_0207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
