theory GOCX_nc_012
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0192: "goc_sub None 192"
  by (goc_eval goc_nc_0192)

lemma goc_nc_0193: "goc_sub None 193"
  by (goc_eval goc_nc_0193)

lemma goc_nc_0194: "goc_sub None 194"
  by (goc_eval goc_nc_0194)

lemma goc_nc_0195: "goc_sub None 195"
  by (goc_eval goc_nc_0195)

lemma goc_nc_0196: "goc_sub None 196"
  by (goc_eval goc_nc_0196)

lemma goc_nc_0197: "goc_sub None 197"
  by (goc_eval goc_nc_0197)

lemma goc_nc_0198: "goc_sub None 198"
  by (goc_eval goc_nc_0198)

lemma goc_nc_0199: "goc_sub None 199"
  by (goc_eval goc_nc_0199)

lemma goc_nc_0200: "goc_sub None 200"
  by (goc_eval goc_nc_0200)

lemma goc_nc_0201: "goc_sub None 201"
  by (goc_eval goc_nc_0201)

lemma goc_nc_0202: "goc_sub None 202"
  by (goc_eval goc_nc_0202)

lemma goc_nc_0203: "goc_sub None 203"
  by (goc_eval goc_nc_0203)

lemma goc_nc_0204: "goc_sub None 204"
  by (goc_eval goc_nc_0204)

lemma goc_nc_0205: "goc_sub None 205"
  by (goc_eval goc_nc_0205)

lemma goc_nc_0206: "goc_sub None 206"
  by (goc_eval goc_nc_0206)

lemma goc_nc_0207: "goc_sub None 207"
  by (goc_eval goc_nc_0207)

lemma gupt_nc_012: "[192..<208] = [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]"
  by (simp add: upt_rec)

lemma gsec_nc_012: "\<forall>j\<in>{16 * 12..<16 * 12 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 12..<16 * 12 + 16}"
  then have "j \<in> set [192..<208]" unfolding set_upt by simp
  then have "j \<in> set [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]" unfolding gupt_nc_012 .
  then show "goc_sub None j" using goc_nc_0192 goc_nc_0193 goc_nc_0194 goc_nc_0195 goc_nc_0196 goc_nc_0197 goc_nc_0198 goc_nc_0199 goc_nc_0200 goc_nc_0201 goc_nc_0202 goc_nc_0203 goc_nc_0204 goc_nc_0205 goc_nc_0206 goc_nc_0207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
