theory OCX_nc_018
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0288: "oc_sub None 288"
  by (oc_eval oc_nc_0288)

lemma oc_nc_0289: "oc_sub None 289"
  by (oc_eval oc_nc_0289)

lemma oc_nc_0290: "oc_sub None 290"
  by (oc_eval oc_nc_0290)

lemma oc_nc_0291: "oc_sub None 291"
  by (oc_eval oc_nc_0291)

lemma oc_nc_0292: "oc_sub None 292"
  by (oc_eval oc_nc_0292)

lemma oc_nc_0293: "oc_sub None 293"
  by (oc_eval oc_nc_0293)

lemma oc_nc_0294: "oc_sub None 294"
  by (oc_eval oc_nc_0294)

lemma oc_nc_0295: "oc_sub None 295"
  by (oc_eval oc_nc_0295)

lemma oc_nc_0296: "oc_sub None 296"
  by (oc_eval oc_nc_0296)

lemma oc_nc_0297: "oc_sub None 297"
  by (oc_eval oc_nc_0297)

lemma oc_nc_0298: "oc_sub None 298"
  by (oc_eval oc_nc_0298)

lemma oc_nc_0299: "oc_sub None 299"
  by (oc_eval oc_nc_0299)

lemma oc_nc_0300: "oc_sub None 300"
  by (oc_eval oc_nc_0300)

lemma oc_nc_0301: "oc_sub None 301"
  by (oc_eval oc_nc_0301)

lemma oc_nc_0302: "oc_sub None 302"
  by (oc_eval oc_nc_0302)

lemma oc_nc_0303: "oc_sub None 303"
  by (oc_eval oc_nc_0303)

lemma upt_nc_018: "[288..<304] = [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]"
  by (simp add: upt_rec)

lemma sec_nc_018: "\<forall>j\<in>{16 * 18..<16 * 18 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 18..<16 * 18 + 16}"
  then have "j \<in> set [288..<304]" unfolding set_upt by simp
  then have "j \<in> set [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]" unfolding upt_nc_018 .
  then show "oc_sub None j" using oc_nc_0288 oc_nc_0289 oc_nc_0290 oc_nc_0291 oc_nc_0292 oc_nc_0293 oc_nc_0294 oc_nc_0295 oc_nc_0296 oc_nc_0297 oc_nc_0298 oc_nc_0299 oc_nc_0300 oc_nc_0301 oc_nc_0302 oc_nc_0303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
