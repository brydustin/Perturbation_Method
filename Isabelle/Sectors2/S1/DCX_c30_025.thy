theory DCX_c30_025
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0400: "dc_sub dc_b30 400"
  by (dc_eval dc_c30_0400)

lemma dc_c30_0401: "dc_sub dc_b30 401"
  by (dc_eval dc_c30_0401)

lemma dc_c30_0402: "dc_sub dc_b30 402"
  by (dc_eval dc_c30_0402)

lemma dc_c30_0403: "dc_sub dc_b30 403"
  by (dc_eval dc_c30_0403)

lemma dc_c30_0404: "dc_sub dc_b30 404"
  by (dc_eval dc_c30_0404)

lemma dc_c30_0405: "dc_sub dc_b30 405"
  by (dc_eval dc_c30_0405)

lemma dc_c30_0406: "dc_sub dc_b30 406"
  by (dc_eval dc_c30_0406)

lemma dc_c30_0407: "dc_sub dc_b30 407"
  by (dc_eval dc_c30_0407)

lemma dc_c30_0408: "dc_sub dc_b30 408"
  by (dc_eval dc_c30_0408)

lemma dc_c30_0409: "dc_sub dc_b30 409"
  by (dc_eval dc_c30_0409)

lemma dc_c30_0410: "dc_sub dc_b30 410"
  by (dc_eval dc_c30_0410)

lemma dc_c30_0411: "dc_sub dc_b30 411"
  by (dc_eval dc_c30_0411)

lemma dc_c30_0412: "dc_sub dc_b30 412"
  by (dc_eval dc_c30_0412)

lemma dc_c30_0413: "dc_sub dc_b30 413"
  by (dc_eval dc_c30_0413)

lemma dc_c30_0414: "dc_sub dc_b30 414"
  by (dc_eval dc_c30_0414)

lemma dc_c30_0415: "dc_sub dc_b30 415"
  by (dc_eval dc_c30_0415)

lemma upt_c30_025: "[400..<416] = [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]"
  by (simp add: upt_rec)

lemma sec_c30_025: "\<forall>j\<in>{16 * 25..<16 * 25 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 25..<16 * 25 + 16}"
  then have "j \<in> set [400..<416]" unfolding set_upt by simp
  then have "j \<in> set [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]" unfolding upt_c30_025 .
  then show "dc_sub dc_b30 j" using dc_c30_0400 dc_c30_0401 dc_c30_0402 dc_c30_0403 dc_c30_0404 dc_c30_0405 dc_c30_0406 dc_c30_0407 dc_c30_0408 dc_c30_0409 dc_c30_0410 dc_c30_0411 dc_c30_0412 dc_c30_0413 dc_c30_0414 dc_c30_0415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
