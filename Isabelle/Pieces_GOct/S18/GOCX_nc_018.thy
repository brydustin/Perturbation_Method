theory GOCX_nc_018
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0288: "goc_sub None 288"
  by (goc_eval goc_nc_0288)

lemma goc_nc_0289: "goc_sub None 289"
  by (goc_eval goc_nc_0289)

lemma goc_nc_0290: "goc_sub None 290"
  by (goc_eval goc_nc_0290)

lemma goc_nc_0291: "goc_sub None 291"
  by (goc_eval goc_nc_0291)

lemma goc_nc_0292: "goc_sub None 292"
  by (goc_eval goc_nc_0292)

lemma goc_nc_0293: "goc_sub None 293"
  by (goc_eval goc_nc_0293)

lemma goc_nc_0294: "goc_sub None 294"
  by (goc_eval goc_nc_0294)

lemma goc_nc_0295: "goc_sub None 295"
  by (goc_eval goc_nc_0295)

lemma goc_nc_0296: "goc_sub None 296"
  by (goc_eval goc_nc_0296)

lemma goc_nc_0297: "goc_sub None 297"
  by (goc_eval goc_nc_0297)

lemma goc_nc_0298: "goc_sub None 298"
  by (goc_eval goc_nc_0298)

lemma goc_nc_0299: "goc_sub None 299"
  by (goc_eval goc_nc_0299)

lemma goc_nc_0300: "goc_sub None 300"
  by (goc_eval goc_nc_0300)

lemma goc_nc_0301: "goc_sub None 301"
  by (goc_eval goc_nc_0301)

lemma goc_nc_0302: "goc_sub None 302"
  by (goc_eval goc_nc_0302)

lemma goc_nc_0303: "goc_sub None 303"
  by (goc_eval goc_nc_0303)

lemma gupt_nc_018: "[288..<304] = [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]"
  by (simp add: upt_rec)

lemma gsec_nc_018: "\<forall>j\<in>{16 * 18..<16 * 18 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 18..<16 * 18 + 16}"
  then have "j \<in> set [288..<304]" unfolding set_upt by simp
  then have "j \<in> set [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]" unfolding gupt_nc_018 .
  then show "goc_sub None j" using goc_nc_0288 goc_nc_0289 goc_nc_0290 goc_nc_0291 goc_nc_0292 goc_nc_0293 goc_nc_0294 goc_nc_0295 goc_nc_0296 goc_nc_0297 goc_nc_0298 goc_nc_0299 goc_nc_0300 goc_nc_0301 goc_nc_0302 goc_nc_0303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
