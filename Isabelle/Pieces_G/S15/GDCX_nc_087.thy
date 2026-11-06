theory GDCX_nc_087
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1392: "gdc_sub None 1392"
  by (gdc_eval gdc_nc_1392)

lemma gdc_nc_1393: "gdc_sub None 1393"
  by (gdc_eval gdc_nc_1393)

lemma gdc_nc_1394: "gdc_sub None 1394"
  by (gdc_eval gdc_nc_1394)

lemma gdc_nc_1395: "gdc_sub None 1395"
  by (gdc_eval gdc_nc_1395)

lemma gdc_nc_1396: "gdc_sub None 1396"
  by (gdc_eval gdc_nc_1396)

lemma gdc_nc_1397: "gdc_sub None 1397"
  by (gdc_eval gdc_nc_1397)

lemma gdc_nc_1398: "gdc_sub None 1398"
  by (gdc_eval gdc_nc_1398)

lemma gdc_nc_1399: "gdc_sub None 1399"
  by (gdc_eval gdc_nc_1399)

lemma gdc_nc_1400: "gdc_sub None 1400"
  by (gdc_eval gdc_nc_1400)

lemma gdc_nc_1401: "gdc_sub None 1401"
  by (gdc_eval gdc_nc_1401)

lemma gdc_nc_1402: "gdc_sub None 1402"
  by (gdc_eval gdc_nc_1402)

lemma gdc_nc_1403: "gdc_sub None 1403"
  by (gdc_eval gdc_nc_1403)

lemma gdc_nc_1404: "gdc_sub None 1404"
  by (gdc_eval gdc_nc_1404)

lemma gdc_nc_1405: "gdc_sub None 1405"
  by (gdc_eval gdc_nc_1405)

lemma gdc_nc_1406: "gdc_sub None 1406"
  by (gdc_eval gdc_nc_1406)

lemma gdc_nc_1407: "gdc_sub None 1407"
  by (gdc_eval gdc_nc_1407)

lemma gupt_nc_087: "[1392..<1408] = [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]"
  by (simp add: upt_rec)

lemma gsec_nc_087: "\<forall>j\<in>{16 * 87..<16 * 87 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 87..<16 * 87 + 16}"
  then have "j \<in> set [1392..<1408]" unfolding set_upt by simp
  then have "j \<in> set [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]" unfolding gupt_nc_087 .
  then show "gdc_sub None j" using gdc_nc_1392 gdc_nc_1393 gdc_nc_1394 gdc_nc_1395 gdc_nc_1396 gdc_nc_1397 gdc_nc_1398 gdc_nc_1399 gdc_nc_1400 gdc_nc_1401 gdc_nc_1402 gdc_nc_1403 gdc_nc_1404 gdc_nc_1405 gdc_nc_1406 gdc_nc_1407
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
