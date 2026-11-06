theory GOCX_nc_143
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2288: "goc_sub None 2288"
  by (goc_eval goc_nc_2288)

lemma goc_nc_2289: "goc_sub None 2289"
  by (goc_eval goc_nc_2289)

lemma goc_nc_2290: "goc_sub None 2290"
  by (goc_eval goc_nc_2290)

lemma goc_nc_2291: "goc_sub None 2291"
  by (goc_eval goc_nc_2291)

lemma goc_nc_2292: "goc_sub None 2292"
  by (goc_eval goc_nc_2292)

lemma goc_nc_2293: "goc_sub None 2293"
  by (goc_eval goc_nc_2293)

lemma goc_nc_2294: "goc_sub None 2294"
  by (goc_eval goc_nc_2294)

lemma goc_nc_2295: "goc_sub None 2295"
  by (goc_eval goc_nc_2295)

lemma goc_nc_2296: "goc_sub None 2296"
  by (goc_eval goc_nc_2296)

lemma goc_nc_2297: "goc_sub None 2297"
  by (goc_eval goc_nc_2297)

lemma goc_nc_2298: "goc_sub None 2298"
  by (goc_eval goc_nc_2298)

lemma goc_nc_2299: "goc_sub None 2299"
  by (goc_eval goc_nc_2299)

lemma goc_nc_2300: "goc_sub None 2300"
  by (goc_eval goc_nc_2300)

lemma goc_nc_2301: "goc_sub None 2301"
  by (goc_eval goc_nc_2301)

lemma goc_nc_2302: "goc_sub None 2302"
  by (goc_eval goc_nc_2302)

lemma goc_nc_2303: "goc_sub None 2303"
  by (goc_eval goc_nc_2303)

lemma gupt_nc_143: "[2288..<2304] = [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]"
  by (simp add: upt_rec)

lemma gsec_nc_143: "\<forall>j\<in>{16 * 143..<16 * 143 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 143..<16 * 143 + 16}"
  then have "j \<in> set [2288..<2304]" unfolding set_upt by simp
  then have "j \<in> set [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]" unfolding gupt_nc_143 .
  then show "goc_sub None j" using goc_nc_2288 goc_nc_2289 goc_nc_2290 goc_nc_2291 goc_nc_2292 goc_nc_2293 goc_nc_2294 goc_nc_2295 goc_nc_2296 goc_nc_2297 goc_nc_2298 goc_nc_2299 goc_nc_2300 goc_nc_2301 goc_nc_2302 goc_nc_2303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
