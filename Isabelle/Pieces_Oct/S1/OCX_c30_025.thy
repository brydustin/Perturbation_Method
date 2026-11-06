theory OCX_c30_025
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0400: "oc_sub oc_b30 400"
  by (oc_eval oc_c30_0400)

lemma oc_c30_0401: "oc_sub oc_b30 401"
  by (oc_eval oc_c30_0401)

lemma oc_c30_0402: "oc_sub oc_b30 402"
  by (oc_eval oc_c30_0402)

lemma oc_c30_0403: "oc_sub oc_b30 403"
  by (oc_eval oc_c30_0403)

lemma oc_c30_0404: "oc_sub oc_b30 404"
  by (oc_eval oc_c30_0404)

lemma oc_c30_0405: "oc_sub oc_b30 405"
  by (oc_eval oc_c30_0405)

lemma oc_c30_0406: "oc_sub oc_b30 406"
  by (oc_eval oc_c30_0406)

lemma oc_c30_0407: "oc_sub oc_b30 407"
  by (oc_eval oc_c30_0407)

lemma oc_c30_0408: "oc_sub oc_b30 408"
  by (oc_eval oc_c30_0408)

lemma oc_c30_0409: "oc_sub oc_b30 409"
  by (oc_eval oc_c30_0409)

lemma oc_c30_0410: "oc_sub oc_b30 410"
  by (oc_eval oc_c30_0410)

lemma oc_c30_0411: "oc_sub oc_b30 411"
  by (oc_eval oc_c30_0411)

lemma oc_c30_0412: "oc_sub oc_b30 412"
  by (oc_eval oc_c30_0412)

lemma oc_c30_0413: "oc_sub oc_b30 413"
  by (oc_eval oc_c30_0413)

lemma oc_c30_0414: "oc_sub oc_b30 414"
  by (oc_eval oc_c30_0414)

lemma oc_c30_0415: "oc_sub oc_b30 415"
  by (oc_eval oc_c30_0415)

lemma upt_c30_025: "[400..<416] = [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]"
  by (simp add: upt_rec)

lemma sec_c30_025: "\<forall>j\<in>{16 * 25..<16 * 25 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 25..<16 * 25 + 16}"
  then have "j \<in> set [400..<416]" unfolding set_upt by simp
  then have "j \<in> set [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]" unfolding upt_c30_025 .
  then show "oc_sub oc_b30 j" using oc_c30_0400 oc_c30_0401 oc_c30_0402 oc_c30_0403 oc_c30_0404 oc_c30_0405 oc_c30_0406 oc_c30_0407 oc_c30_0408 oc_c30_0409 oc_c30_0410 oc_c30_0411 oc_c30_0412 oc_c30_0413 oc_c30_0414 oc_c30_0415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
