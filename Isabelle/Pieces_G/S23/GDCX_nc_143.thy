theory GDCX_nc_143
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2288: "gdc_sub None 2288"
  by (gdc_eval gdc_nc_2288)

lemma gdc_nc_2289: "gdc_sub None 2289"
  by (gdc_eval gdc_nc_2289)

lemma gdc_nc_2290: "gdc_sub None 2290"
  by (gdc_eval gdc_nc_2290)

lemma gdc_nc_2291: "gdc_sub None 2291"
  by (gdc_eval gdc_nc_2291)

lemma gdc_nc_2292: "gdc_sub None 2292"
  by (gdc_eval gdc_nc_2292)

lemma gdc_nc_2293: "gdc_sub None 2293"
  by (gdc_eval gdc_nc_2293)

lemma gdc_nc_2294: "gdc_sub None 2294"
  by (gdc_eval gdc_nc_2294)

lemma gdc_nc_2295: "gdc_sub None 2295"
  by (gdc_eval gdc_nc_2295)

lemma gdc_nc_2296: "gdc_sub None 2296"
  by (gdc_eval gdc_nc_2296)

lemma gdc_nc_2297: "gdc_sub None 2297"
  by (gdc_eval gdc_nc_2297)

lemma gdc_nc_2298: "gdc_sub None 2298"
  by (gdc_eval gdc_nc_2298)

lemma gdc_nc_2299: "gdc_sub None 2299"
  by (gdc_eval gdc_nc_2299)

lemma gdc_nc_2300: "gdc_sub None 2300"
  by (gdc_eval gdc_nc_2300)

lemma gdc_nc_2301: "gdc_sub None 2301"
  by (gdc_eval gdc_nc_2301)

lemma gdc_nc_2302: "gdc_sub None 2302"
  by (gdc_eval gdc_nc_2302)

lemma gdc_nc_2303: "gdc_sub None 2303"
  by (gdc_eval gdc_nc_2303)

lemma gupt_nc_143: "[2288..<2304] = [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]"
  by (simp add: upt_rec)

lemma gsec_nc_143: "\<forall>j\<in>{16 * 143..<16 * 143 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 143..<16 * 143 + 16}"
  then have "j \<in> set [2288..<2304]" unfolding set_upt by simp
  then have "j \<in> set [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]" unfolding gupt_nc_143 .
  then show "gdc_sub None j" using gdc_nc_2288 gdc_nc_2289 gdc_nc_2290 gdc_nc_2291 gdc_nc_2292 gdc_nc_2293 gdc_nc_2294 gdc_nc_2295 gdc_nc_2296 gdc_nc_2297 gdc_nc_2298 gdc_nc_2299 gdc_nc_2300 gdc_nc_2301 gdc_nc_2302 gdc_nc_2303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
