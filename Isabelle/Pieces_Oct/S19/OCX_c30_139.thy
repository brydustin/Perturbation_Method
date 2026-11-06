theory OCX_c30_139
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2224: "oc_sub oc_b30 2224"
  by (oc_eval oc_c30_2224)

lemma oc_c30_2225: "oc_sub oc_b30 2225"
  by (oc_eval oc_c30_2225)

lemma oc_c30_2226: "oc_sub oc_b30 2226"
  by (oc_eval oc_c30_2226)

lemma oc_c30_2227: "oc_sub oc_b30 2227"
  by (oc_eval oc_c30_2227)

lemma oc_c30_2228: "oc_sub oc_b30 2228"
  by (oc_eval oc_c30_2228)

lemma oc_c30_2229: "oc_sub oc_b30 2229"
  by (oc_eval oc_c30_2229)

lemma oc_c30_2230: "oc_sub oc_b30 2230"
  by (oc_eval oc_c30_2230)

lemma oc_c30_2231: "oc_sub oc_b30 2231"
  by (oc_eval oc_c30_2231)

lemma oc_c30_2232: "oc_sub oc_b30 2232"
  by (oc_eval oc_c30_2232)

lemma oc_c30_2233: "oc_sub oc_b30 2233"
  by (oc_eval oc_c30_2233)

lemma oc_c30_2234: "oc_sub oc_b30 2234"
  by (oc_eval oc_c30_2234)

lemma oc_c30_2235: "oc_sub oc_b30 2235"
  by (oc_eval oc_c30_2235)

lemma oc_c30_2236: "oc_sub oc_b30 2236"
  by (oc_eval oc_c30_2236)

lemma oc_c30_2237: "oc_sub oc_b30 2237"
  by (oc_eval oc_c30_2237)

lemma oc_c30_2238: "oc_sub oc_b30 2238"
  by (oc_eval oc_c30_2238)

lemma oc_c30_2239: "oc_sub oc_b30 2239"
  by (oc_eval oc_c30_2239)

lemma upt_c30_139: "[2224..<2240] = [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]"
  by (simp add: upt_rec)

lemma sec_c30_139: "\<forall>j\<in>{16 * 139..<16 * 139 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 139..<16 * 139 + 16}"
  then have "j \<in> set [2224..<2240]" unfolding set_upt by simp
  then have "j \<in> set [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]" unfolding upt_c30_139 .
  then show "oc_sub oc_b30 j" using oc_c30_2224 oc_c30_2225 oc_c30_2226 oc_c30_2227 oc_c30_2228 oc_c30_2229 oc_c30_2230 oc_c30_2231 oc_c30_2232 oc_c30_2233 oc_c30_2234 oc_c30_2235 oc_c30_2236 oc_c30_2237 oc_c30_2238 oc_c30_2239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
