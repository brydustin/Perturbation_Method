theory OCX_c30_150
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2400: "oc_sub oc_b30 2400"
  by (oc_eval oc_c30_2400)

lemma oc_c30_2401: "oc_sub oc_b30 2401"
  by (oc_eval oc_c30_2401)

lemma oc_c30_2402: "oc_sub oc_b30 2402"
  by (oc_eval oc_c30_2402)

lemma oc_c30_2403: "oc_sub oc_b30 2403"
  by (oc_eval oc_c30_2403)

lemma oc_c30_2404: "oc_sub oc_b30 2404"
  by (oc_eval oc_c30_2404)

lemma oc_c30_2405: "oc_sub oc_b30 2405"
  by (oc_eval oc_c30_2405)

lemma oc_c30_2406: "oc_sub oc_b30 2406"
  by (oc_eval oc_c30_2406)

lemma oc_c30_2407: "oc_sub oc_b30 2407"
  by (oc_eval oc_c30_2407)

lemma oc_c30_2408: "oc_sub oc_b30 2408"
  by (oc_eval oc_c30_2408)

lemma oc_c30_2409: "oc_sub oc_b30 2409"
  by (oc_eval oc_c30_2409)

lemma oc_c30_2410: "oc_sub oc_b30 2410"
  by (oc_eval oc_c30_2410)

lemma oc_c30_2411: "oc_sub oc_b30 2411"
  by (oc_eval oc_c30_2411)

lemma oc_c30_2412: "oc_sub oc_b30 2412"
  by (oc_eval oc_c30_2412)

lemma oc_c30_2413: "oc_sub oc_b30 2413"
  by (oc_eval oc_c30_2413)

lemma oc_c30_2414: "oc_sub oc_b30 2414"
  by (oc_eval oc_c30_2414)

lemma oc_c30_2415: "oc_sub oc_b30 2415"
  by (oc_eval oc_c30_2415)

lemma upt_c30_150: "[2400..<2416] = [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]"
  by (simp add: upt_rec)

lemma sec_c30_150: "\<forall>j\<in>{16 * 150..<16 * 150 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 150..<16 * 150 + 16}"
  then have "j \<in> set [2400..<2416]" unfolding set_upt by simp
  then have "j \<in> set [2400, 2401, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2410, 2411, 2412, 2413, 2414, 2415]" unfolding upt_c30_150 .
  then show "oc_sub oc_b30 j" using oc_c30_2400 oc_c30_2401 oc_c30_2402 oc_c30_2403 oc_c30_2404 oc_c30_2405 oc_c30_2406 oc_c30_2407 oc_c30_2408 oc_c30_2409 oc_c30_2410 oc_c30_2411 oc_c30_2412 oc_c30_2413 oc_c30_2414 oc_c30_2415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
