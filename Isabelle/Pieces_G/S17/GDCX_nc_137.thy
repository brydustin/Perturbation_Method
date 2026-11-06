theory GDCX_nc_137
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2192: "gdc_sub None 2192"
  by (gdc_eval gdc_nc_2192)

lemma gdc_nc_2193: "gdc_sub None 2193"
  by (gdc_eval gdc_nc_2193)

lemma gdc_nc_2194: "gdc_sub None 2194"
  by (gdc_eval gdc_nc_2194)

lemma gdc_nc_2195: "gdc_sub None 2195"
  by (gdc_eval gdc_nc_2195)

lemma gdc_nc_2196: "gdc_sub None 2196"
  by (gdc_eval gdc_nc_2196)

lemma gdc_nc_2197: "gdc_sub None 2197"
  by (gdc_eval gdc_nc_2197)

lemma gdc_nc_2198: "gdc_sub None 2198"
  by (gdc_eval gdc_nc_2198)

lemma gdc_nc_2199: "gdc_sub None 2199"
  by (gdc_eval gdc_nc_2199)

lemma gdc_nc_2200: "gdc_sub None 2200"
  by (gdc_eval gdc_nc_2200)

lemma gdc_nc_2201: "gdc_sub None 2201"
  by (gdc_eval gdc_nc_2201)

lemma gdc_nc_2202: "gdc_sub None 2202"
  by (gdc_eval gdc_nc_2202)

lemma gdc_nc_2203: "gdc_sub None 2203"
  by (gdc_eval gdc_nc_2203)

lemma gdc_nc_2204: "gdc_sub None 2204"
  by (gdc_eval gdc_nc_2204)

lemma gdc_nc_2205: "gdc_sub None 2205"
  by (gdc_eval gdc_nc_2205)

lemma gdc_nc_2206: "gdc_sub None 2206"
  by (gdc_eval gdc_nc_2206)

lemma gdc_nc_2207: "gdc_sub None 2207"
  by (gdc_eval gdc_nc_2207)

lemma gupt_nc_137: "[2192..<2208] = [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]"
  by (simp add: upt_rec)

lemma gsec_nc_137: "\<forall>j\<in>{16 * 137..<16 * 137 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 137..<16 * 137 + 16}"
  then have "j \<in> set [2192..<2208]" unfolding set_upt by simp
  then have "j \<in> set [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]" unfolding gupt_nc_137 .
  then show "gdc_sub None j" using gdc_nc_2192 gdc_nc_2193 gdc_nc_2194 gdc_nc_2195 gdc_nc_2196 gdc_nc_2197 gdc_nc_2198 gdc_nc_2199 gdc_nc_2200 gdc_nc_2201 gdc_nc_2202 gdc_nc_2203 gdc_nc_2204 gdc_nc_2205 gdc_nc_2206 gdc_nc_2207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
