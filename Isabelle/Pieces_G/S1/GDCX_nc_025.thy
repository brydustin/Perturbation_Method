theory GDCX_nc_025
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0400: "gdc_sub None 400"
  by (gdc_eval gdc_nc_0400)

lemma gdc_nc_0401: "gdc_sub None 401"
  by (gdc_eval gdc_nc_0401)

lemma gdc_nc_0402: "gdc_sub None 402"
  by (gdc_eval gdc_nc_0402)

lemma gdc_nc_0403: "gdc_sub None 403"
  by (gdc_eval gdc_nc_0403)

lemma gdc_nc_0404: "gdc_sub None 404"
  by (gdc_eval gdc_nc_0404)

lemma gdc_nc_0405: "gdc_sub None 405"
  by (gdc_eval gdc_nc_0405)

lemma gdc_nc_0406: "gdc_sub None 406"
  by (gdc_eval gdc_nc_0406)

lemma gdc_nc_0407: "gdc_sub None 407"
  by (gdc_eval gdc_nc_0407)

lemma gdc_nc_0408: "gdc_sub None 408"
  by (gdc_eval gdc_nc_0408)

lemma gdc_nc_0409: "gdc_sub None 409"
  by (gdc_eval gdc_nc_0409)

lemma gdc_nc_0410: "gdc_sub None 410"
  by (gdc_eval gdc_nc_0410)

lemma gdc_nc_0411: "gdc_sub None 411"
  by (gdc_eval gdc_nc_0411)

lemma gdc_nc_0412: "gdc_sub None 412"
  by (gdc_eval gdc_nc_0412)

lemma gdc_nc_0413: "gdc_sub None 413"
  by (gdc_eval gdc_nc_0413)

lemma gdc_nc_0414: "gdc_sub None 414"
  by (gdc_eval gdc_nc_0414)

lemma gdc_nc_0415: "gdc_sub None 415"
  by (gdc_eval gdc_nc_0415)

lemma gupt_nc_025: "[400..<416] = [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]"
  by (simp add: upt_rec)

lemma gsec_nc_025: "\<forall>j\<in>{16 * 25..<16 * 25 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 25..<16 * 25 + 16}"
  then have "j \<in> set [400..<416]" unfolding set_upt by simp
  then have "j \<in> set [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]" unfolding gupt_nc_025 .
  then show "gdc_sub None j" using gdc_nc_0400 gdc_nc_0401 gdc_nc_0402 gdc_nc_0403 gdc_nc_0404 gdc_nc_0405 gdc_nc_0406 gdc_nc_0407 gdc_nc_0408 gdc_nc_0409 gdc_nc_0410 gdc_nc_0411 gdc_nc_0412 gdc_nc_0413 gdc_nc_0414 gdc_nc_0415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
