theory GOCX_nc_025
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0400: "goc_sub None 400"
  by (goc_eval goc_nc_0400)

lemma goc_nc_0401: "goc_sub None 401"
  by (goc_eval goc_nc_0401)

lemma goc_nc_0402: "goc_sub None 402"
  by (goc_eval goc_nc_0402)

lemma goc_nc_0403: "goc_sub None 403"
  by (goc_eval goc_nc_0403)

lemma goc_nc_0404: "goc_sub None 404"
  by (goc_eval goc_nc_0404)

lemma goc_nc_0405: "goc_sub None 405"
  by (goc_eval goc_nc_0405)

lemma goc_nc_0406: "goc_sub None 406"
  by (goc_eval goc_nc_0406)

lemma goc_nc_0407: "goc_sub None 407"
  by (goc_eval goc_nc_0407)

lemma goc_nc_0408: "goc_sub None 408"
  by (goc_eval goc_nc_0408)

lemma goc_nc_0409: "goc_sub None 409"
  by (goc_eval goc_nc_0409)

lemma goc_nc_0410: "goc_sub None 410"
  by (goc_eval goc_nc_0410)

lemma goc_nc_0411: "goc_sub None 411"
  by (goc_eval goc_nc_0411)

lemma goc_nc_0412: "goc_sub None 412"
  by (goc_eval goc_nc_0412)

lemma goc_nc_0413: "goc_sub None 413"
  by (goc_eval goc_nc_0413)

lemma goc_nc_0414: "goc_sub None 414"
  by (goc_eval goc_nc_0414)

lemma goc_nc_0415: "goc_sub None 415"
  by (goc_eval goc_nc_0415)

lemma gupt_nc_025: "[400..<416] = [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]"
  by (simp add: upt_rec)

lemma gsec_nc_025: "\<forall>j\<in>{16 * 25..<16 * 25 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 25..<16 * 25 + 16}"
  then have "j \<in> set [400..<416]" unfolding set_upt by simp
  then have "j \<in> set [400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]" unfolding gupt_nc_025 .
  then show "goc_sub None j" using goc_nc_0400 goc_nc_0401 goc_nc_0402 goc_nc_0403 goc_nc_0404 goc_nc_0405 goc_nc_0406 goc_nc_0407 goc_nc_0408 goc_nc_0409 goc_nc_0410 goc_nc_0411 goc_nc_0412 goc_nc_0413 goc_nc_0414 goc_nc_0415
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
