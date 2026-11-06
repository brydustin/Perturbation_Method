theory GDCX_nc_012
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0192: "gdc_sub None 192"
  by (gdc_eval gdc_nc_0192)

lemma gdc_nc_0193: "gdc_sub None 193"
  by (gdc_eval gdc_nc_0193)

lemma gdc_nc_0194: "gdc_sub None 194"
  by (gdc_eval gdc_nc_0194)

lemma gdc_nc_0195: "gdc_sub None 195"
  by (gdc_eval gdc_nc_0195)

lemma gdc_nc_0196: "gdc_sub None 196"
  by (gdc_eval gdc_nc_0196)

lemma gdc_nc_0197: "gdc_sub None 197"
  by (gdc_eval gdc_nc_0197)

lemma gdc_nc_0198: "gdc_sub None 198"
  by (gdc_eval gdc_nc_0198)

lemma gdc_nc_0199: "gdc_sub None 199"
  by (gdc_eval gdc_nc_0199)

lemma gdc_nc_0200: "gdc_sub None 200"
  by (gdc_eval gdc_nc_0200)

lemma gdc_nc_0201: "gdc_sub None 201"
  by (gdc_eval gdc_nc_0201)

lemma gdc_nc_0202: "gdc_sub None 202"
  by (gdc_eval gdc_nc_0202)

lemma gdc_nc_0203: "gdc_sub None 203"
  by (gdc_eval gdc_nc_0203)

lemma gdc_nc_0204: "gdc_sub None 204"
  by (gdc_eval gdc_nc_0204)

lemma gdc_nc_0205: "gdc_sub None 205"
  by (gdc_eval gdc_nc_0205)

lemma gdc_nc_0206: "gdc_sub None 206"
  by (gdc_eval gdc_nc_0206)

lemma gdc_nc_0207: "gdc_sub None 207"
  by (gdc_eval gdc_nc_0207)

lemma gupt_nc_012: "[192..<208] = [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]"
  by (simp add: upt_rec)

lemma gsec_nc_012: "\<forall>j\<in>{16 * 12..<16 * 12 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 12..<16 * 12 + 16}"
  then have "j \<in> set [192..<208]" unfolding set_upt by simp
  then have "j \<in> set [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]" unfolding gupt_nc_012 .
  then show "gdc_sub None j" using gdc_nc_0192 gdc_nc_0193 gdc_nc_0194 gdc_nc_0195 gdc_nc_0196 gdc_nc_0197 gdc_nc_0198 gdc_nc_0199 gdc_nc_0200 gdc_nc_0201 gdc_nc_0202 gdc_nc_0203 gdc_nc_0204 gdc_nc_0205 gdc_nc_0206 gdc_nc_0207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
