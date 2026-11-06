theory OCX_nc_139
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2224: "oc_sub None 2224"
  by (oc_eval oc_nc_2224)

lemma oc_nc_2225: "oc_sub None 2225"
  by (oc_eval oc_nc_2225)

lemma oc_nc_2226: "oc_sub None 2226"
  by (oc_eval oc_nc_2226)

lemma oc_nc_2227: "oc_sub None 2227"
  by (oc_eval oc_nc_2227)

lemma oc_nc_2228: "oc_sub None 2228"
  by (oc_eval oc_nc_2228)

lemma oc_nc_2229: "oc_sub None 2229"
  by (oc_eval oc_nc_2229)

lemma oc_nc_2230: "oc_sub None 2230"
  by (oc_eval oc_nc_2230)

lemma oc_nc_2231: "oc_sub None 2231"
  by (oc_eval oc_nc_2231)

lemma oc_nc_2232: "oc_sub None 2232"
  by (oc_eval oc_nc_2232)

lemma oc_nc_2233: "oc_sub None 2233"
  by (oc_eval oc_nc_2233)

lemma oc_nc_2234: "oc_sub None 2234"
  by (oc_eval oc_nc_2234)

lemma oc_nc_2235: "oc_sub None 2235"
  by (oc_eval oc_nc_2235)

lemma oc_nc_2236: "oc_sub None 2236"
  by (oc_eval oc_nc_2236)

lemma oc_nc_2237: "oc_sub None 2237"
  by (oc_eval oc_nc_2237)

lemma oc_nc_2238: "oc_sub None 2238"
  by (oc_eval oc_nc_2238)

lemma oc_nc_2239: "oc_sub None 2239"
  by (oc_eval oc_nc_2239)

lemma upt_nc_139: "[2224..<2240] = [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]"
  by (simp add: upt_rec)

lemma sec_nc_139: "\<forall>j\<in>{16 * 139..<16 * 139 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 139..<16 * 139 + 16}"
  then have "j \<in> set [2224..<2240]" unfolding set_upt by simp
  then have "j \<in> set [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]" unfolding upt_nc_139 .
  then show "oc_sub None j" using oc_nc_2224 oc_nc_2225 oc_nc_2226 oc_nc_2227 oc_nc_2228 oc_nc_2229 oc_nc_2230 oc_nc_2231 oc_nc_2232 oc_nc_2233 oc_nc_2234 oc_nc_2235 oc_nc_2236 oc_nc_2237 oc_nc_2238 oc_nc_2239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
