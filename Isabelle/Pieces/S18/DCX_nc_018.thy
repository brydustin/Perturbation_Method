theory DCX_nc_018
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0288: "dc_sub None 288"
  by (dc_eval dc_nc_0288)

lemma dc_nc_0289: "dc_sub None 289"
  by (dc_eval dc_nc_0289)

lemma dc_nc_0290: "dc_sub None 290"
  by (dc_eval dc_nc_0290)

lemma dc_nc_0291: "dc_sub None 291"
  by (dc_eval dc_nc_0291)

lemma dc_nc_0292: "dc_sub None 292"
  by (dc_eval dc_nc_0292)

lemma dc_nc_0293: "dc_sub None 293"
  by (dc_eval dc_nc_0293)

lemma dc_nc_0294: "dc_sub None 294"
  by (dc_eval dc_nc_0294)

lemma dc_nc_0295: "dc_sub None 295"
  by (dc_eval dc_nc_0295)

lemma dc_nc_0296: "dc_sub None 296"
  by (dc_eval dc_nc_0296)

lemma dc_nc_0297: "dc_sub None 297"
  by (dc_eval dc_nc_0297)

lemma dc_nc_0298: "dc_sub None 298"
  by (dc_eval dc_nc_0298)

lemma dc_nc_0299: "dc_sub None 299"
  by (dc_eval dc_nc_0299)

lemma dc_nc_0300: "dc_sub None 300"
  by (dc_eval dc_nc_0300)

lemma dc_nc_0301: "dc_sub None 301"
  by (dc_eval dc_nc_0301)

lemma dc_nc_0302: "dc_sub None 302"
  by (dc_eval dc_nc_0302)

lemma dc_nc_0303: "dc_sub None 303"
  by (dc_eval dc_nc_0303)

lemma upt_nc_018: "[288..<304] = [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]"
  by (simp add: upt_rec)

lemma sec_nc_018: "\<forall>j\<in>{16 * 18..<16 * 18 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 18..<16 * 18 + 16}"
  then have "j \<in> set [288..<304]" unfolding set_upt by simp
  then have "j \<in> set [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]" unfolding upt_nc_018 .
  then show "dc_sub None j" using dc_nc_0288 dc_nc_0289 dc_nc_0290 dc_nc_0291 dc_nc_0292 dc_nc_0293 dc_nc_0294 dc_nc_0295 dc_nc_0296 dc_nc_0297 dc_nc_0298 dc_nc_0299 dc_nc_0300 dc_nc_0301 dc_nc_0302 dc_nc_0303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
