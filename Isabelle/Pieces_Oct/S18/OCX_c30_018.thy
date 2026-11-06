theory OCX_c30_018
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0288: "oc_sub oc_b30 288"
  by (oc_eval oc_c30_0288)

lemma oc_c30_0289: "oc_sub oc_b30 289"
  by (oc_eval oc_c30_0289)

lemma oc_c30_0290: "oc_sub oc_b30 290"
  by (oc_eval oc_c30_0290)

lemma oc_c30_0291: "oc_sub oc_b30 291"
  by (oc_eval oc_c30_0291)

lemma oc_c30_0292: "oc_sub oc_b30 292"
  by (oc_eval oc_c30_0292)

lemma oc_c30_0293: "oc_sub oc_b30 293"
  by (oc_eval oc_c30_0293)

lemma oc_c30_0294: "oc_sub oc_b30 294"
  by (oc_eval oc_c30_0294)

lemma oc_c30_0295: "oc_sub oc_b30 295"
  by (oc_eval oc_c30_0295)

lemma oc_c30_0296: "oc_sub oc_b30 296"
  by (oc_eval oc_c30_0296)

lemma oc_c30_0297: "oc_sub oc_b30 297"
  by (oc_eval oc_c30_0297)

lemma oc_c30_0298: "oc_sub oc_b30 298"
  by (oc_eval oc_c30_0298)

lemma oc_c30_0299: "oc_sub oc_b30 299"
  by (oc_eval oc_c30_0299)

lemma oc_c30_0300: "oc_sub oc_b30 300"
  by (oc_eval oc_c30_0300)

lemma oc_c30_0301: "oc_sub oc_b30 301"
  by (oc_eval oc_c30_0301)

lemma oc_c30_0302: "oc_sub oc_b30 302"
  by (oc_eval oc_c30_0302)

lemma oc_c30_0303: "oc_sub oc_b30 303"
  by (oc_eval oc_c30_0303)

lemma upt_c30_018: "[288..<304] = [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]"
  by (simp add: upt_rec)

lemma sec_c30_018: "\<forall>j\<in>{16 * 18..<16 * 18 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 18..<16 * 18 + 16}"
  then have "j \<in> set [288..<304]" unfolding set_upt by simp
  then have "j \<in> set [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]" unfolding upt_c30_018 .
  then show "oc_sub oc_b30 j" using oc_c30_0288 oc_c30_0289 oc_c30_0290 oc_c30_0291 oc_c30_0292 oc_c30_0293 oc_c30_0294 oc_c30_0295 oc_c30_0296 oc_c30_0297 oc_c30_0298 oc_c30_0299 oc_c30_0300 oc_c30_0301 oc_c30_0302 oc_c30_0303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
