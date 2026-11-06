theory OCX_nc_137
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2192: "oc_sub None 2192"
  by (oc_eval oc_nc_2192)

lemma oc_nc_2193: "oc_sub None 2193"
  by (oc_eval oc_nc_2193)

lemma oc_nc_2194: "oc_sub None 2194"
  by (oc_eval oc_nc_2194)

lemma oc_nc_2195: "oc_sub None 2195"
  by (oc_eval oc_nc_2195)

lemma oc_nc_2196: "oc_sub None 2196"
  by (oc_eval oc_nc_2196)

lemma oc_nc_2197: "oc_sub None 2197"
  by (oc_eval oc_nc_2197)

lemma oc_nc_2198: "oc_sub None 2198"
  by (oc_eval oc_nc_2198)

lemma oc_nc_2199: "oc_sub None 2199"
  by (oc_eval oc_nc_2199)

lemma oc_nc_2200: "oc_sub None 2200"
  by (oc_eval oc_nc_2200)

lemma oc_nc_2201: "oc_sub None 2201"
  by (oc_eval oc_nc_2201)

lemma oc_nc_2202: "oc_sub None 2202"
  by (oc_eval oc_nc_2202)

lemma oc_nc_2203: "oc_sub None 2203"
  by (oc_eval oc_nc_2203)

lemma oc_nc_2204: "oc_sub None 2204"
  by (oc_eval oc_nc_2204)

lemma oc_nc_2205: "oc_sub None 2205"
  by (oc_eval oc_nc_2205)

lemma oc_nc_2206: "oc_sub None 2206"
  by (oc_eval oc_nc_2206)

lemma oc_nc_2207: "oc_sub None 2207"
  by (oc_eval oc_nc_2207)

lemma upt_nc_137: "[2192..<2208] = [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]"
  by (simp add: upt_rec)

lemma sec_nc_137: "\<forall>j\<in>{16 * 137..<16 * 137 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 137..<16 * 137 + 16}"
  then have "j \<in> set [2192..<2208]" unfolding set_upt by simp
  then have "j \<in> set [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]" unfolding upt_nc_137 .
  then show "oc_sub None j" using oc_nc_2192 oc_nc_2193 oc_nc_2194 oc_nc_2195 oc_nc_2196 oc_nc_2197 oc_nc_2198 oc_nc_2199 oc_nc_2200 oc_nc_2201 oc_nc_2202 oc_nc_2203 oc_nc_2204 oc_nc_2205 oc_nc_2206 oc_nc_2207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
