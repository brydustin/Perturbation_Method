theory GDCX_nc_150
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2400: "gdc_sub None 2400"
  by (gdc_eval gdc_nc_2400)

lemma gdc_nc_2401: "gdc_sub None 2401"
  by (gdc_eval gdc_nc_2401)

lemma gdc_nc_2402: "gdc_sub None 2402"
  by (gdc_eval gdc_nc_2402)

lemma gdc_nc_2403: "gdc_sub None 2403"
  by (gdc_eval gdc_nc_2403)

lemma gdc_nc_2404: "gdc_sub None 2404"
  by (gdc_eval gdc_nc_2404)

lemma gdc_nc_2405: "gdc_sub None 2405"
  by (gdc_eval gdc_nc_2405)

lemma gdc_nc_2406: "gdc_sub None 2406"
  by (gdc_eval gdc_nc_2406)

lemma gdc_nc_2407: "gdc_sub None 2407"
  by (gdc_eval gdc_nc_2407)

lemma gdc_nc_2408: "gdc_sub None 2408"
  by (gdc_eval gdc_nc_2408)

lemma gdc_nc_2409: "gdc_sub None 2409"
  by (gdc_eval gdc_nc_2409)

lemma gdc_nc_2410: "gdc_sub None 2410"
  by (gdc_eval gdc_nc_2410)

lemma gdc_nc_2411: "gdc_sub None 2411"
  by (gdc_eval gdc_nc_2411)

lemma gdc_nc_2412: "gdc_sub None 2412"
  by (gdc_eval gdc_nc_2412)

lemma gdc_nc_2413: "gdc_sub None 2413"
  by (gdc_eval gdc_nc_2413)

lemma gdc_nc_2414: "gdc_sub None 2414"
  by (gdc_eval gdc_nc_2414)

lemma gdc_nc_2415: "gdc_sub None 2415"
  by (gdc_eval gdc_nc_2415)

lemma gupt_nc_150: "[2400..<2416] = [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]"
  by (simp add: upt_rec)

lemma gsec_nc_150: "\<forall>j\<in>{16 * 150..<16 * 150 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 150..<16 * 150 + 16}"
  then have "j \<in> set [2400..<2416]" unfolding set_upt by simp
  then have "j \<in> set [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]" unfolding gupt_nc_150 .
  then show "gdc_sub None j" using gdc_nc_2400 gdc_nc_2401 gdc_nc_2402 gdc_nc_2403 gdc_nc_2404 gdc_nc_2405 gdc_nc_2406 gdc_nc_2407 gdc_nc_2408 gdc_nc_2409 gdc_nc_2410 gdc_nc_2411 gdc_nc_2412 gdc_nc_2413 gdc_nc_2414 gdc_nc_2415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
