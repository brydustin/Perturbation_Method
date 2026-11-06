theory DCX_nc_025
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0400: "dc_sub None 400"
  by (dc_eval dc_nc_0400)

lemma dc_nc_0401: "dc_sub None 401"
  by (dc_eval dc_nc_0401)

lemma dc_nc_0402: "dc_sub None 402"
  by (dc_eval dc_nc_0402)

lemma dc_nc_0403: "dc_sub None 403"
  by (dc_eval dc_nc_0403)

lemma dc_nc_0404: "dc_sub None 404"
  by (dc_eval dc_nc_0404)

lemma dc_nc_0405: "dc_sub None 405"
  by (dc_eval dc_nc_0405)

lemma dc_nc_0406: "dc_sub None 406"
  by (dc_eval dc_nc_0406)

lemma dc_nc_0407: "dc_sub None 407"
  by (dc_eval dc_nc_0407)

lemma dc_nc_0408: "dc_sub None 408"
  by (dc_eval dc_nc_0408)

lemma dc_nc_0409: "dc_sub None 409"
  by (dc_eval dc_nc_0409)

lemma dc_nc_0410: "dc_sub None 410"
  by (dc_eval dc_nc_0410)

lemma dc_nc_0411: "dc_sub None 411"
  by (dc_eval dc_nc_0411)

lemma dc_nc_0412: "dc_sub None 412"
  by (dc_eval dc_nc_0412)

lemma dc_nc_0413: "dc_sub None 413"
  by (dc_eval dc_nc_0413)

lemma dc_nc_0414: "dc_sub None 414"
  by (dc_eval dc_nc_0414)

lemma dc_nc_0415: "dc_sub None 415"
  by (dc_eval dc_nc_0415)

lemma upt_nc_025: "[400..<416] = [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]"
  by (simp add: upt_rec)

lemma sec_nc_025: "\<forall>j\<in>{16 * 25..<16 * 25 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 25..<16 * 25 + 16}"
  then have "j \<in> set [400..<416]" unfolding set_upt by simp
  then have "j \<in> set [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]" unfolding upt_nc_025 .
  then show "dc_sub None j" using dc_nc_0400 dc_nc_0401 dc_nc_0402 dc_nc_0403 dc_nc_0404 dc_nc_0405 dc_nc_0406 dc_nc_0407 dc_nc_0408 dc_nc_0409 dc_nc_0410 dc_nc_0411 dc_nc_0412 dc_nc_0413 dc_nc_0414 dc_nc_0415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
