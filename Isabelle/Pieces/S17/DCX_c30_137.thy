theory DCX_c30_137
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2192: "dc_sub dc_b30 2192"
  by (dc_eval dc_c30_2192)

lemma dc_c30_2193: "dc_sub dc_b30 2193"
  by (dc_eval dc_c30_2193)

lemma dc_c30_2194: "dc_sub dc_b30 2194"
  by (dc_eval dc_c30_2194)

lemma dc_c30_2195: "dc_sub dc_b30 2195"
  by (dc_eval dc_c30_2195)

lemma dc_c30_2196: "dc_sub dc_b30 2196"
  by (dc_eval dc_c30_2196)

lemma dc_c30_2197: "dc_sub dc_b30 2197"
  by (dc_eval dc_c30_2197)

lemma dc_c30_2198: "dc_sub dc_b30 2198"
  by (dc_eval dc_c30_2198)

lemma dc_c30_2199: "dc_sub dc_b30 2199"
  by (dc_eval dc_c30_2199)

lemma dc_c30_2200: "dc_sub dc_b30 2200"
  by (dc_eval dc_c30_2200)

lemma dc_c30_2201: "dc_sub dc_b30 2201"
  by (dc_eval dc_c30_2201)

lemma dc_c30_2202: "dc_sub dc_b30 2202"
  by (dc_eval dc_c30_2202)

lemma dc_c30_2203: "dc_sub dc_b30 2203"
  by (dc_eval dc_c30_2203)

lemma dc_c30_2204: "dc_sub dc_b30 2204"
  by (dc_eval dc_c30_2204)

lemma dc_c30_2205: "dc_sub dc_b30 2205"
  by (dc_eval dc_c30_2205)

lemma dc_c30_2206: "dc_sub dc_b30 2206"
  by (dc_eval dc_c30_2206)

lemma dc_c30_2207: "dc_sub dc_b30 2207"
  by (dc_eval dc_c30_2207)

lemma upt_c30_137: "[2192..<2208] = [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]"
  by (simp add: upt_rec)

lemma sec_c30_137: "\<forall>j\<in>{16 * 137..<16 * 137 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 137..<16 * 137 + 16}"
  then have "j \<in> set [2192..<2208]" unfolding set_upt by simp
  then have "j \<in> set [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]" unfolding upt_c30_137 .
  then show "dc_sub dc_b30 j" using dc_c30_2192 dc_c30_2193 dc_c30_2194 dc_c30_2195 dc_c30_2196 dc_c30_2197 dc_c30_2198 dc_c30_2199 dc_c30_2200 dc_c30_2201 dc_c30_2202 dc_c30_2203 dc_c30_2204 dc_c30_2205 dc_c30_2206 dc_c30_2207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
