theory DCX_c30_150
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2400: "dc_sub dc_b30 2400"
  by (dc_eval dc_c30_2400)

lemma dc_c30_2401: "dc_sub dc_b30 2401"
  by (dc_eval dc_c30_2401)

lemma dc_c30_2402: "dc_sub dc_b30 2402"
  by (dc_eval dc_c30_2402)

lemma dc_c30_2403: "dc_sub dc_b30 2403"
  by (dc_eval dc_c30_2403)

lemma dc_c30_2404: "dc_sub dc_b30 2404"
  by (dc_eval dc_c30_2404)

lemma dc_c30_2405: "dc_sub dc_b30 2405"
  by (dc_eval dc_c30_2405)

lemma dc_c30_2406: "dc_sub dc_b30 2406"
  by (dc_eval dc_c30_2406)

lemma dc_c30_2407: "dc_sub dc_b30 2407"
  by (dc_eval dc_c30_2407)

lemma dc_c30_2408: "dc_sub dc_b30 2408"
  by (dc_eval dc_c30_2408)

lemma dc_c30_2409: "dc_sub dc_b30 2409"
  by (dc_eval dc_c30_2409)

lemma dc_c30_2410: "dc_sub dc_b30 2410"
  by (dc_eval dc_c30_2410)

lemma dc_c30_2411: "dc_sub dc_b30 2411"
  by (dc_eval dc_c30_2411)

lemma dc_c30_2412: "dc_sub dc_b30 2412"
  by (dc_eval dc_c30_2412)

lemma dc_c30_2413: "dc_sub dc_b30 2413"
  by (dc_eval dc_c30_2413)

lemma dc_c30_2414: "dc_sub dc_b30 2414"
  by (dc_eval dc_c30_2414)

lemma dc_c30_2415: "dc_sub dc_b30 2415"
  by (dc_eval dc_c30_2415)

lemma upt_c30_150: "[2400..<2416] = [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]"
  by (simp add: upt_rec)

lemma sec_c30_150: "\<forall>j\<in>{16 * 150..<16 * 150 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 150..<16 * 150 + 16}"
  then have "j \<in> set [2400..<2416]" unfolding set_upt by simp
  then have "j \<in> set [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]" unfolding upt_c30_150 .
  then show "dc_sub dc_b30 j" using dc_c30_2400 dc_c30_2401 dc_c30_2402 dc_c30_2403 dc_c30_2404 dc_c30_2405 dc_c30_2406 dc_c30_2407 dc_c30_2408 dc_c30_2409 dc_c30_2410 dc_c30_2411 dc_c30_2412 dc_c30_2413 dc_c30_2414 dc_c30_2415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
