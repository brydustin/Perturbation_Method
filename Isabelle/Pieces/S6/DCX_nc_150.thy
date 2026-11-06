theory DCX_nc_150
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2400: "dc_sub None 2400"
  by (dc_eval dc_nc_2400)

lemma dc_nc_2401: "dc_sub None 2401"
  by (dc_eval dc_nc_2401)

lemma dc_nc_2402: "dc_sub None 2402"
  by (dc_eval dc_nc_2402)

lemma dc_nc_2403: "dc_sub None 2403"
  by (dc_eval dc_nc_2403)

lemma dc_nc_2404: "dc_sub None 2404"
  by (dc_eval dc_nc_2404)

lemma dc_nc_2405: "dc_sub None 2405"
  by (dc_eval dc_nc_2405)

lemma dc_nc_2406: "dc_sub None 2406"
  by (dc_eval dc_nc_2406)

lemma dc_nc_2407: "dc_sub None 2407"
  by (dc_eval dc_nc_2407)

lemma dc_nc_2408: "dc_sub None 2408"
  by (dc_eval dc_nc_2408)

lemma dc_nc_2409: "dc_sub None 2409"
  by (dc_eval dc_nc_2409)

lemma dc_nc_2410: "dc_sub None 2410"
  by (dc_eval dc_nc_2410)

lemma dc_nc_2411: "dc_sub None 2411"
  by (dc_eval dc_nc_2411)

lemma dc_nc_2412: "dc_sub None 2412"
  by (dc_eval dc_nc_2412)

lemma dc_nc_2413: "dc_sub None 2413"
  by (dc_eval dc_nc_2413)

lemma dc_nc_2414: "dc_sub None 2414"
  by (dc_eval dc_nc_2414)

lemma dc_nc_2415: "dc_sub None 2415"
  by (dc_eval dc_nc_2415)

lemma upt_nc_150: "[2400..<2416] = [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]"
  by (simp add: upt_rec)

lemma sec_nc_150: "\<forall>j\<in>{16 * 150..<16 * 150 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 150..<16 * 150 + 16}"
  then have "j \<in> set [2400..<2416]" unfolding set_upt by simp
  then have "j \<in> set [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]" unfolding upt_nc_150 .
  then show "dc_sub None j" using dc_nc_2400 dc_nc_2401 dc_nc_2402 dc_nc_2403 dc_nc_2404 dc_nc_2405 dc_nc_2406 dc_nc_2407 dc_nc_2408 dc_nc_2409 dc_nc_2410 dc_nc_2411 dc_nc_2412 dc_nc_2413 dc_nc_2414 dc_nc_2415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
