theory DCX_nc_012
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0192: "dc_sub None 192"
  by (dc_eval dc_nc_0192)

lemma dc_nc_0193: "dc_sub None 193"
  by (dc_eval dc_nc_0193)

lemma dc_nc_0194: "dc_sub None 194"
  by (dc_eval dc_nc_0194)

lemma dc_nc_0195: "dc_sub None 195"
  by (dc_eval dc_nc_0195)

lemma dc_nc_0196: "dc_sub None 196"
  by (dc_eval dc_nc_0196)

lemma dc_nc_0197: "dc_sub None 197"
  by (dc_eval dc_nc_0197)

lemma dc_nc_0198: "dc_sub None 198"
  by (dc_eval dc_nc_0198)

lemma dc_nc_0199: "dc_sub None 199"
  by (dc_eval dc_nc_0199)

lemma dc_nc_0200: "dc_sub None 200"
  by (dc_eval dc_nc_0200)

lemma dc_nc_0201: "dc_sub None 201"
  by (dc_eval dc_nc_0201)

lemma dc_nc_0202: "dc_sub None 202"
  by (dc_eval dc_nc_0202)

lemma dc_nc_0203: "dc_sub None 203"
  by (dc_eval dc_nc_0203)

lemma dc_nc_0204: "dc_sub None 204"
  by (dc_eval dc_nc_0204)

lemma dc_nc_0205: "dc_sub None 205"
  by (dc_eval dc_nc_0205)

lemma dc_nc_0206: "dc_sub None 206"
  by (dc_eval dc_nc_0206)

lemma dc_nc_0207: "dc_sub None 207"
  by (dc_eval dc_nc_0207)

lemma upt_nc_012: "[192..<208] = [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]"
  by (simp add: upt_rec)

lemma sec_nc_012: "\<forall>j\<in>{16 * 12..<16 * 12 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 12..<16 * 12 + 16}"
  then have "j \<in> set [192..<208]" unfolding set_upt by simp
  then have "j \<in> set [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]" unfolding upt_nc_012 .
  then show "dc_sub None j" using dc_nc_0192 dc_nc_0193 dc_nc_0194 dc_nc_0195 dc_nc_0196 dc_nc_0197 dc_nc_0198 dc_nc_0199 dc_nc_0200 dc_nc_0201 dc_nc_0202 dc_nc_0203 dc_nc_0204 dc_nc_0205 dc_nc_0206 dc_nc_0207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
