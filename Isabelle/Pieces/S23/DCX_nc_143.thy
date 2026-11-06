theory DCX_nc_143
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2288: "dc_sub None 2288"
  by (dc_eval dc_nc_2288)

lemma dc_nc_2289: "dc_sub None 2289"
  by (dc_eval dc_nc_2289)

lemma dc_nc_2290: "dc_sub None 2290"
  by (dc_eval dc_nc_2290)

lemma dc_nc_2291: "dc_sub None 2291"
  by (dc_eval dc_nc_2291)

lemma dc_nc_2292: "dc_sub None 2292"
  by (dc_eval dc_nc_2292)

lemma dc_nc_2293: "dc_sub None 2293"
  by (dc_eval dc_nc_2293)

lemma dc_nc_2294: "dc_sub None 2294"
  by (dc_eval dc_nc_2294)

lemma dc_nc_2295: "dc_sub None 2295"
  by (dc_eval dc_nc_2295)

lemma dc_nc_2296: "dc_sub None 2296"
  by (dc_eval dc_nc_2296)

lemma dc_nc_2297: "dc_sub None 2297"
  by (dc_eval dc_nc_2297)

lemma dc_nc_2298: "dc_sub None 2298"
  by (dc_eval dc_nc_2298)

lemma dc_nc_2299: "dc_sub None 2299"
  by (dc_eval dc_nc_2299)

lemma dc_nc_2300: "dc_sub None 2300"
  by (dc_eval dc_nc_2300)

lemma dc_nc_2301: "dc_sub None 2301"
  by (dc_eval dc_nc_2301)

lemma dc_nc_2302: "dc_sub None 2302"
  by (dc_eval dc_nc_2302)

lemma dc_nc_2303: "dc_sub None 2303"
  by (dc_eval dc_nc_2303)

lemma upt_nc_143: "[2288..<2304] = [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]"
  by (simp add: upt_rec)

lemma sec_nc_143: "\<forall>j\<in>{16 * 143..<16 * 143 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 143..<16 * 143 + 16}"
  then have "j \<in> set [2288..<2304]" unfolding set_upt by simp
  then have "j \<in> set [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]" unfolding upt_nc_143 .
  then show "dc_sub None j" using dc_nc_2288 dc_nc_2289 dc_nc_2290 dc_nc_2291 dc_nc_2292 dc_nc_2293 dc_nc_2294 dc_nc_2295 dc_nc_2296 dc_nc_2297 dc_nc_2298 dc_nc_2299 dc_nc_2300 dc_nc_2301 dc_nc_2302 dc_nc_2303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
