theory GOCX_nc_150
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2400: "goc_sub None 2400"
  by (goc_eval goc_nc_2400)

lemma goc_nc_2401: "goc_sub None 2401"
  by (goc_eval goc_nc_2401)

lemma goc_nc_2402: "goc_sub None 2402"
  by (goc_eval goc_nc_2402)

lemma goc_nc_2403: "goc_sub None 2403"
  by (goc_eval goc_nc_2403)

lemma goc_nc_2404: "goc_sub None 2404"
  by (goc_eval goc_nc_2404)

lemma goc_nc_2405: "goc_sub None 2405"
  by (goc_eval goc_nc_2405)

lemma goc_nc_2406: "goc_sub None 2406"
  by (goc_eval goc_nc_2406)

lemma goc_nc_2407: "goc_sub None 2407"
  by (goc_eval goc_nc_2407)

lemma goc_nc_2408: "goc_sub None 2408"
  by (goc_eval goc_nc_2408)

lemma goc_nc_2409: "goc_sub None 2409"
  by (goc_eval goc_nc_2409)

lemma goc_nc_2410: "goc_sub None 2410"
  by (goc_eval goc_nc_2410)

lemma goc_nc_2411: "goc_sub None 2411"
  by (goc_eval goc_nc_2411)

lemma goc_nc_2412: "goc_sub None 2412"
  by (goc_eval goc_nc_2412)

lemma goc_nc_2413: "goc_sub None 2413"
  by (goc_eval goc_nc_2413)

lemma goc_nc_2414: "goc_sub None 2414"
  by (goc_eval goc_nc_2414)

lemma goc_nc_2415: "goc_sub None 2415"
  by (goc_eval goc_nc_2415)

lemma gupt_nc_150: "[2400..<2416] = [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]"
  by (simp add: upt_rec)

lemma gsec_nc_150: "\<forall>j\<in>{16 * 150..<16 * 150 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 150..<16 * 150 + 16}"
  then have "j \<in> set [2400..<2416]" unfolding set_upt by simp
  then have "j \<in> set [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]" unfolding gupt_nc_150 .
  then show "goc_sub None j" using goc_nc_2400 goc_nc_2401 goc_nc_2402 goc_nc_2403 goc_nc_2404 goc_nc_2405 goc_nc_2406 goc_nc_2407 goc_nc_2408 goc_nc_2409 goc_nc_2410 goc_nc_2411 goc_nc_2412 goc_nc_2413 goc_nc_2414 goc_nc_2415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
