theory GDCX_nc_139
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2224: "gdc_sub None 2224"
  by (gdc_eval gdc_nc_2224)

lemma gdc_nc_2225: "gdc_sub None 2225"
  by (gdc_eval gdc_nc_2225)

lemma gdc_nc_2226: "gdc_sub None 2226"
  by (gdc_eval gdc_nc_2226)

lemma gdc_nc_2227: "gdc_sub None 2227"
  by (gdc_eval gdc_nc_2227)

lemma gdc_nc_2228: "gdc_sub None 2228"
  by (gdc_eval gdc_nc_2228)

lemma gdc_nc_2229: "gdc_sub None 2229"
  by (gdc_eval gdc_nc_2229)

lemma gdc_nc_2230: "gdc_sub None 2230"
  by (gdc_eval gdc_nc_2230)

lemma gdc_nc_2231: "gdc_sub None 2231"
  by (gdc_eval gdc_nc_2231)

lemma gdc_nc_2232: "gdc_sub None 2232"
  by (gdc_eval gdc_nc_2232)

lemma gdc_nc_2233: "gdc_sub None 2233"
  by (gdc_eval gdc_nc_2233)

lemma gdc_nc_2234: "gdc_sub None 2234"
  by (gdc_eval gdc_nc_2234)

lemma gdc_nc_2235: "gdc_sub None 2235"
  by (gdc_eval gdc_nc_2235)

lemma gdc_nc_2236: "gdc_sub None 2236"
  by (gdc_eval gdc_nc_2236)

lemma gdc_nc_2237: "gdc_sub None 2237"
  by (gdc_eval gdc_nc_2237)

lemma gdc_nc_2238: "gdc_sub None 2238"
  by (gdc_eval gdc_nc_2238)

lemma gdc_nc_2239: "gdc_sub None 2239"
  by (gdc_eval gdc_nc_2239)

lemma gupt_nc_139: "[2224..<2240] = [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]"
  by (simp add: upt_rec)

lemma gsec_nc_139: "\<forall>j\<in>{16 * 139..<16 * 139 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 139..<16 * 139 + 16}"
  then have "j \<in> set [2224..<2240]" unfolding set_upt by simp
  then have "j \<in> set [2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]" unfolding gupt_nc_139 .
  then show "gdc_sub None j" using gdc_nc_2224 gdc_nc_2225 gdc_nc_2226 gdc_nc_2227 gdc_nc_2228 gdc_nc_2229 gdc_nc_2230 gdc_nc_2231 gdc_nc_2232 gdc_nc_2233 gdc_nc_2234 gdc_nc_2235 gdc_nc_2236 gdc_nc_2237 gdc_nc_2238 gdc_nc_2239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
