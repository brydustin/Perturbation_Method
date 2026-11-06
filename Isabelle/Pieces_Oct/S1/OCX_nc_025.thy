theory OCX_nc_025
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0400: "oc_sub None 400"
  by (oc_eval oc_nc_0400)

lemma oc_nc_0401: "oc_sub None 401"
  by (oc_eval oc_nc_0401)

lemma oc_nc_0402: "oc_sub None 402"
  by (oc_eval oc_nc_0402)

lemma oc_nc_0403: "oc_sub None 403"
  by (oc_eval oc_nc_0403)

lemma oc_nc_0404: "oc_sub None 404"
  by (oc_eval oc_nc_0404)

lemma oc_nc_0405: "oc_sub None 405"
  by (oc_eval oc_nc_0405)

lemma oc_nc_0406: "oc_sub None 406"
  by (oc_eval oc_nc_0406)

lemma oc_nc_0407: "oc_sub None 407"
  by (oc_eval oc_nc_0407)

lemma oc_nc_0408: "oc_sub None 408"
  by (oc_eval oc_nc_0408)

lemma oc_nc_0409: "oc_sub None 409"
  by (oc_eval oc_nc_0409)

lemma oc_nc_0410: "oc_sub None 410"
  by (oc_eval oc_nc_0410)

lemma oc_nc_0411: "oc_sub None 411"
  by (oc_eval oc_nc_0411)

lemma oc_nc_0412: "oc_sub None 412"
  by (oc_eval oc_nc_0412)

lemma oc_nc_0413: "oc_sub None 413"
  by (oc_eval oc_nc_0413)

lemma oc_nc_0414: "oc_sub None 414"
  by (oc_eval oc_nc_0414)

lemma oc_nc_0415: "oc_sub None 415"
  by (oc_eval oc_nc_0415)

lemma upt_nc_025: "[400..<416] = [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]"
  by (simp add: upt_rec)

lemma sec_nc_025: "\<forall>j\<in>{16 * 25..<16 * 25 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 25..<16 * 25 + 16}"
  then have "j \<in> set [400..<416]" unfolding set_upt by simp
  then have "j \<in> set [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]" unfolding upt_nc_025 .
  then show "oc_sub None j" using oc_nc_0400 oc_nc_0401 oc_nc_0402 oc_nc_0403 oc_nc_0404 oc_nc_0405 oc_nc_0406 oc_nc_0407 oc_nc_0408 oc_nc_0409 oc_nc_0410 oc_nc_0411 oc_nc_0412 oc_nc_0413 oc_nc_0414 oc_nc_0415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
