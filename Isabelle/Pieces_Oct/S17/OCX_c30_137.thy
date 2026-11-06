theory OCX_c30_137
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2192: "oc_sub oc_b30 2192"
  by (oc_eval oc_c30_2192)

lemma oc_c30_2193: "oc_sub oc_b30 2193"
  by (oc_eval oc_c30_2193)

lemma oc_c30_2194: "oc_sub oc_b30 2194"
  by (oc_eval oc_c30_2194)

lemma oc_c30_2195: "oc_sub oc_b30 2195"
  by (oc_eval oc_c30_2195)

lemma oc_c30_2196: "oc_sub oc_b30 2196"
  by (oc_eval oc_c30_2196)

lemma oc_c30_2197: "oc_sub oc_b30 2197"
  by (oc_eval oc_c30_2197)

lemma oc_c30_2198: "oc_sub oc_b30 2198"
  by (oc_eval oc_c30_2198)

lemma oc_c30_2199: "oc_sub oc_b30 2199"
  by (oc_eval oc_c30_2199)

lemma oc_c30_2200: "oc_sub oc_b30 2200"
  by (oc_eval oc_c30_2200)

lemma oc_c30_2201: "oc_sub oc_b30 2201"
  by (oc_eval oc_c30_2201)

lemma oc_c30_2202: "oc_sub oc_b30 2202"
  by (oc_eval oc_c30_2202)

lemma oc_c30_2203: "oc_sub oc_b30 2203"
  by (oc_eval oc_c30_2203)

lemma oc_c30_2204: "oc_sub oc_b30 2204"
  by (oc_eval oc_c30_2204)

lemma oc_c30_2205: "oc_sub oc_b30 2205"
  by (oc_eval oc_c30_2205)

lemma oc_c30_2206: "oc_sub oc_b30 2206"
  by (oc_eval oc_c30_2206)

lemma oc_c30_2207: "oc_sub oc_b30 2207"
  by (oc_eval oc_c30_2207)

lemma upt_c30_137: "[2192..<2208] = [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]"
  by (simp add: upt_rec)

lemma sec_c30_137: "\<forall>j\<in>{16 * 137..<16 * 137 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 137..<16 * 137 + 16}"
  then have "j \<in> set [2192..<2208]" unfolding set_upt by simp
  then have "j \<in> set [2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207]" unfolding upt_c30_137 .
  then show "oc_sub oc_b30 j" using oc_c30_2192 oc_c30_2193 oc_c30_2194 oc_c30_2195 oc_c30_2196 oc_c30_2197 oc_c30_2198 oc_c30_2199 oc_c30_2200 oc_c30_2201 oc_c30_2202 oc_c30_2203 oc_c30_2204 oc_c30_2205 oc_c30_2206 oc_c30_2207
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
