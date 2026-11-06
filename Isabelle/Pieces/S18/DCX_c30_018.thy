theory DCX_c30_018
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0288: "dc_sub dc_b30 288"
  by (dc_eval dc_c30_0288)

lemma dc_c30_0289: "dc_sub dc_b30 289"
  by (dc_eval dc_c30_0289)

lemma dc_c30_0290: "dc_sub dc_b30 290"
  by (dc_eval dc_c30_0290)

lemma dc_c30_0291: "dc_sub dc_b30 291"
  by (dc_eval dc_c30_0291)

lemma dc_c30_0292: "dc_sub dc_b30 292"
  by (dc_eval dc_c30_0292)

lemma dc_c30_0293: "dc_sub dc_b30 293"
  by (dc_eval dc_c30_0293)

lemma dc_c30_0294: "dc_sub dc_b30 294"
  by (dc_eval dc_c30_0294)

lemma dc_c30_0295: "dc_sub dc_b30 295"
  by (dc_eval dc_c30_0295)

lemma dc_c30_0296: "dc_sub dc_b30 296"
  by (dc_eval dc_c30_0296)

lemma dc_c30_0297: "dc_sub dc_b30 297"
  by (dc_eval dc_c30_0297)

lemma dc_c30_0298: "dc_sub dc_b30 298"
  by (dc_eval dc_c30_0298)

lemma dc_c30_0299: "dc_sub dc_b30 299"
  by (dc_eval dc_c30_0299)

lemma dc_c30_0300: "dc_sub dc_b30 300"
  by (dc_eval dc_c30_0300)

lemma dc_c30_0301: "dc_sub dc_b30 301"
  by (dc_eval dc_c30_0301)

lemma dc_c30_0302: "dc_sub dc_b30 302"
  by (dc_eval dc_c30_0302)

lemma dc_c30_0303: "dc_sub dc_b30 303"
  by (dc_eval dc_c30_0303)

lemma upt_c30_018: "[288..<304] = [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]"
  by (simp add: upt_rec)

lemma sec_c30_018: "\<forall>j\<in>{16 * 18..<16 * 18 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 18..<16 * 18 + 16}"
  then have "j \<in> set [288..<304]" unfolding set_upt by simp
  then have "j \<in> set [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]" unfolding upt_c30_018 .
  then show "dc_sub dc_b30 j" using dc_c30_0288 dc_c30_0289 dc_c30_0290 dc_c30_0291 dc_c30_0292 dc_c30_0293 dc_c30_0294 dc_c30_0295 dc_c30_0296 dc_c30_0297 dc_c30_0298 dc_c30_0299 dc_c30_0300 dc_c30_0301 dc_c30_0302 dc_c30_0303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
