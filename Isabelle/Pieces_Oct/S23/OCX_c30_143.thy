theory OCX_c30_143
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2288: "oc_sub oc_b30 2288"
  by (oc_eval oc_c30_2288)

lemma oc_c30_2289: "oc_sub oc_b30 2289"
  by (oc_eval oc_c30_2289)

lemma oc_c30_2290: "oc_sub oc_b30 2290"
  by (oc_eval oc_c30_2290)

lemma oc_c30_2291: "oc_sub oc_b30 2291"
  by (oc_eval oc_c30_2291)

lemma oc_c30_2292: "oc_sub oc_b30 2292"
  by (oc_eval oc_c30_2292)

lemma oc_c30_2293: "oc_sub oc_b30 2293"
  by (oc_eval oc_c30_2293)

lemma oc_c30_2294: "oc_sub oc_b30 2294"
  by (oc_eval oc_c30_2294)

lemma oc_c30_2295: "oc_sub oc_b30 2295"
  by (oc_eval oc_c30_2295)

lemma oc_c30_2296: "oc_sub oc_b30 2296"
  by (oc_eval oc_c30_2296)

lemma oc_c30_2297: "oc_sub oc_b30 2297"
  by (oc_eval oc_c30_2297)

lemma oc_c30_2298: "oc_sub oc_b30 2298"
  by (oc_eval oc_c30_2298)

lemma oc_c30_2299: "oc_sub oc_b30 2299"
  by (oc_eval oc_c30_2299)

lemma oc_c30_2300: "oc_sub oc_b30 2300"
  by (oc_eval oc_c30_2300)

lemma oc_c30_2301: "oc_sub oc_b30 2301"
  by (oc_eval oc_c30_2301)

lemma oc_c30_2302: "oc_sub oc_b30 2302"
  by (oc_eval oc_c30_2302)

lemma oc_c30_2303: "oc_sub oc_b30 2303"
  by (oc_eval oc_c30_2303)

lemma upt_c30_143: "[2288..<2304] = [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]"
  by (simp add: upt_rec)

lemma sec_c30_143: "\<forall>j\<in>{16 * 143..<16 * 143 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 143..<16 * 143 + 16}"
  then have "j \<in> set [2288..<2304]" unfolding set_upt by simp
  then have "j \<in> set [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]" unfolding upt_c30_143 .
  then show "oc_sub oc_b30 j" using oc_c30_2288 oc_c30_2289 oc_c30_2290 oc_c30_2291 oc_c30_2292 oc_c30_2293 oc_c30_2294 oc_c30_2295 oc_c30_2296 oc_c30_2297 oc_c30_2298 oc_c30_2299 oc_c30_2300 oc_c30_2301 oc_c30_2302 oc_c30_2303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
