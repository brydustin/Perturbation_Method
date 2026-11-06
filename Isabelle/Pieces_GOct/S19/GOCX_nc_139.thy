theory GOCX_nc_139
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2224: "goc_sub None 2224"
  by (goc_eval goc_nc_2224)

lemma goc_nc_2225: "goc_sub None 2225"
  by (goc_eval goc_nc_2225)

lemma goc_nc_2226: "goc_sub None 2226"
  by (goc_eval goc_nc_2226)

lemma goc_nc_2227: "goc_sub None 2227"
  by (goc_eval goc_nc_2227)

lemma goc_nc_2228: "goc_sub None 2228"
  by (goc_eval goc_nc_2228)

lemma goc_nc_2229: "goc_sub None 2229"
  by (goc_eval goc_nc_2229)

lemma goc_nc_2230: "goc_sub None 2230"
  by (goc_eval goc_nc_2230)

lemma goc_nc_2231: "goc_sub None 2231"
  by (goc_eval goc_nc_2231)

lemma goc_nc_2232: "goc_sub None 2232"
  by (goc_eval goc_nc_2232)

lemma goc_nc_2233: "goc_sub None 2233"
  by (goc_eval goc_nc_2233)

lemma goc_nc_2234: "goc_sub None 2234"
  by (goc_eval goc_nc_2234)

lemma goc_nc_2235: "goc_sub None 2235"
  by (goc_eval goc_nc_2235)

lemma goc_nc_2236: "goc_sub None 2236"
  by (goc_eval goc_nc_2236)

lemma goc_nc_2237: "goc_sub None 2237"
  by (goc_eval goc_nc_2237)

lemma goc_nc_2238: "goc_sub None 2238"
  by (goc_eval goc_nc_2238)

lemma goc_nc_2239: "goc_sub None 2239"
  by (goc_eval goc_nc_2239)

lemma gupt_nc_139: "[2224..<2240] = [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]"
  by (simp add: upt_rec)

lemma gsec_nc_139: "\<forall>j\<in>{16 * 139..<16 * 139 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 139..<16 * 139 + 16}"
  then have "j \<in> set [2224..<2240]" unfolding set_upt by simp
  then have "j \<in> set [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]" unfolding gupt_nc_139 .
  then show "goc_sub None j" using goc_nc_2224 goc_nc_2225 goc_nc_2226 goc_nc_2227 goc_nc_2228 goc_nc_2229 goc_nc_2230 goc_nc_2231 goc_nc_2232 goc_nc_2233 goc_nc_2234 goc_nc_2235 goc_nc_2236 goc_nc_2237 goc_nc_2238 goc_nc_2239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
