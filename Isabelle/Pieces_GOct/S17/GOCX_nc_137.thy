theory GOCX_nc_137
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2192: "goc_sub None 2192"
  by (goc_eval goc_nc_2192)

lemma goc_nc_2193: "goc_sub None 2193"
  by (goc_eval goc_nc_2193)

lemma goc_nc_2194: "goc_sub None 2194"
  by (goc_eval goc_nc_2194)

lemma goc_nc_2195: "goc_sub None 2195"
  by (goc_eval goc_nc_2195)

lemma goc_nc_2196: "goc_sub None 2196"
  by (goc_eval goc_nc_2196)

lemma goc_nc_2197: "goc_sub None 2197"
  by (goc_eval goc_nc_2197)

lemma goc_nc_2198: "goc_sub None 2198"
  by (goc_eval goc_nc_2198)

lemma goc_nc_2199: "goc_sub None 2199"
  by (goc_eval goc_nc_2199)

lemma goc_nc_2200: "goc_sub None 2200"
  by (goc_eval goc_nc_2200)

lemma goc_nc_2201: "goc_sub None 2201"
  by (goc_eval goc_nc_2201)

lemma goc_nc_2202: "goc_sub None 2202"
  by (goc_eval goc_nc_2202)

lemma goc_nc_2203: "goc_sub None 2203"
  by (goc_eval goc_nc_2203)

lemma goc_nc_2204: "goc_sub None 2204"
  by (goc_eval goc_nc_2204)

lemma goc_nc_2205: "goc_sub None 2205"
  by (goc_eval goc_nc_2205)

lemma goc_nc_2206: "goc_sub None 2206"
  by (goc_eval goc_nc_2206)

lemma goc_nc_2207: "goc_sub None 2207"
  by (goc_eval goc_nc_2207)

lemma gupt_nc_137: "[2192..<2208] = [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]"
  by (simp add: upt_rec)

lemma gsec_nc_137: "\<forall>j\<in>{16 * 137..<16 * 137 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 137..<16 * 137 + 16}"
  then have "j \<in> set [2192..<2208]" unfolding set_upt by simp
  then have "j \<in> set [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]" unfolding gupt_nc_137 .
  then show "goc_sub None j" using goc_nc_2192 goc_nc_2193 goc_nc_2194 goc_nc_2195 goc_nc_2196 goc_nc_2197 goc_nc_2198 goc_nc_2199 goc_nc_2200 goc_nc_2201 goc_nc_2202 goc_nc_2203 goc_nc_2204 goc_nc_2205 goc_nc_2206 goc_nc_2207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
