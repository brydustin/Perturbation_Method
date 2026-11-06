theory GDCX_nc_018
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0288: "gdc_sub None 288"
  by (gdc_eval gdc_nc_0288)

lemma gdc_nc_0289: "gdc_sub None 289"
  by (gdc_eval gdc_nc_0289)

lemma gdc_nc_0290: "gdc_sub None 290"
  by (gdc_eval gdc_nc_0290)

lemma gdc_nc_0291: "gdc_sub None 291"
  by (gdc_eval gdc_nc_0291)

lemma gdc_nc_0292: "gdc_sub None 292"
  by (gdc_eval gdc_nc_0292)

lemma gdc_nc_0293: "gdc_sub None 293"
  by (gdc_eval gdc_nc_0293)

lemma gdc_nc_0294: "gdc_sub None 294"
  by (gdc_eval gdc_nc_0294)

lemma gdc_nc_0295: "gdc_sub None 295"
  by (gdc_eval gdc_nc_0295)

lemma gdc_nc_0296: "gdc_sub None 296"
  by (gdc_eval gdc_nc_0296)

lemma gdc_nc_0297: "gdc_sub None 297"
  by (gdc_eval gdc_nc_0297)

lemma gdc_nc_0298: "gdc_sub None 298"
  by (gdc_eval gdc_nc_0298)

lemma gdc_nc_0299: "gdc_sub None 299"
  by (gdc_eval gdc_nc_0299)

lemma gdc_nc_0300: "gdc_sub None 300"
  by (gdc_eval gdc_nc_0300)

lemma gdc_nc_0301: "gdc_sub None 301"
  by (gdc_eval gdc_nc_0301)

lemma gdc_nc_0302: "gdc_sub None 302"
  by (gdc_eval gdc_nc_0302)

lemma gdc_nc_0303: "gdc_sub None 303"
  by (gdc_eval gdc_nc_0303)

lemma gupt_nc_018: "[288..<304] = [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]"
  by (simp add: upt_rec)

lemma gsec_nc_018: "\<forall>j\<in>{16 * 18..<16 * 18 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 18..<16 * 18 + 16}"
  then have "j \<in> set [288..<304]" unfolding set_upt by simp
  then have "j \<in> set [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303]" unfolding gupt_nc_018 .
  then show "gdc_sub None j" using gdc_nc_0288 gdc_nc_0289 gdc_nc_0290 gdc_nc_0291 gdc_nc_0292 gdc_nc_0293 gdc_nc_0294 gdc_nc_0295 gdc_nc_0296 gdc_nc_0297 gdc_nc_0298 gdc_nc_0299 gdc_nc_0300 gdc_nc_0301 gdc_nc_0302 gdc_nc_0303
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
