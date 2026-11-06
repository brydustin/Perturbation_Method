theory DCX_c30_143
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2288: "dc_sub dc_b30 2288"
  by (dc_eval dc_c30_2288)

lemma dc_c30_2289: "dc_sub dc_b30 2289"
  by (dc_eval dc_c30_2289)

lemma dc_c30_2290: "dc_sub dc_b30 2290"
  by (dc_eval dc_c30_2290)

lemma dc_c30_2291: "dc_sub dc_b30 2291"
  by (dc_eval dc_c30_2291)

lemma dc_c30_2292: "dc_sub dc_b30 2292"
  by (dc_eval dc_c30_2292)

lemma dc_c30_2293: "dc_sub dc_b30 2293"
  by (dc_eval dc_c30_2293)

lemma dc_c30_2294: "dc_sub dc_b30 2294"
  by (dc_eval dc_c30_2294)

lemma dc_c30_2295: "dc_sub dc_b30 2295"
  by (dc_eval dc_c30_2295)

lemma dc_c30_2296: "dc_sub dc_b30 2296"
  by (dc_eval dc_c30_2296)

lemma dc_c30_2297: "dc_sub dc_b30 2297"
  by (dc_eval dc_c30_2297)

lemma dc_c30_2298: "dc_sub dc_b30 2298"
  by (dc_eval dc_c30_2298)

lemma dc_c30_2299: "dc_sub dc_b30 2299"
  by (dc_eval dc_c30_2299)

lemma dc_c30_2300: "dc_sub dc_b30 2300"
  by (dc_eval dc_c30_2300)

lemma dc_c30_2301: "dc_sub dc_b30 2301"
  by (dc_eval dc_c30_2301)

lemma dc_c30_2302: "dc_sub dc_b30 2302"
  by (dc_eval dc_c30_2302)

lemma dc_c30_2303: "dc_sub dc_b30 2303"
  by (dc_eval dc_c30_2303)

lemma upt_c30_143: "[2288..<2304] = [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]"
  by (simp add: upt_rec)

lemma sec_c30_143: "\<forall>j\<in>{16 * 143..<16 * 143 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 143..<16 * 143 + 16}"
  then have "j \<in> set [2288..<2304]" unfolding set_upt by simp
  then have "j \<in> set [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]" unfolding upt_c30_143 .
  then show "dc_sub dc_b30 j" using dc_c30_2288 dc_c30_2289 dc_c30_2290 dc_c30_2291 dc_c30_2292 dc_c30_2293 dc_c30_2294 dc_c30_2295 dc_c30_2296 dc_c30_2297 dc_c30_2298 dc_c30_2299 dc_c30_2300 dc_c30_2301 dc_c30_2302 dc_c30_2303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
