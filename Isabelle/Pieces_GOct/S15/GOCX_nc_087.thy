theory GOCX_nc_087
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1392: "goc_sub None 1392"
  by (goc_eval goc_nc_1392)

lemma goc_nc_1393: "goc_sub None 1393"
  by (goc_eval goc_nc_1393)

lemma goc_nc_1394: "goc_sub None 1394"
  by (goc_eval goc_nc_1394)

lemma goc_nc_1395: "goc_sub None 1395"
  by (goc_eval goc_nc_1395)

lemma goc_nc_1396: "goc_sub None 1396"
  by (goc_eval goc_nc_1396)

lemma goc_nc_1397: "goc_sub None 1397"
  by (goc_eval goc_nc_1397)

lemma goc_nc_1398: "goc_sub None 1398"
  by (goc_eval goc_nc_1398)

lemma goc_nc_1399: "goc_sub None 1399"
  by (goc_eval goc_nc_1399)

lemma goc_nc_1400: "goc_sub None 1400"
  by (goc_eval goc_nc_1400)

lemma goc_nc_1401: "goc_sub None 1401"
  by (goc_eval goc_nc_1401)

lemma goc_nc_1402: "goc_sub None 1402"
  by (goc_eval goc_nc_1402)

lemma goc_nc_1403: "goc_sub None 1403"
  by (goc_eval goc_nc_1403)

lemma goc_nc_1404: "goc_sub None 1404"
  by (goc_eval goc_nc_1404)

lemma goc_nc_1405: "goc_sub None 1405"
  by (goc_eval goc_nc_1405)

lemma goc_nc_1406: "goc_sub None 1406"
  by (goc_eval goc_nc_1406)

lemma goc_nc_1407: "goc_sub None 1407"
  by (goc_eval goc_nc_1407)

lemma gupt_nc_087: "[1392..<1408] = [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]"
  by (simp add: upt_rec)

lemma gsec_nc_087: "\<forall>j\<in>{16 * 87..<16 * 87 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 87..<16 * 87 + 16}"
  then have "j \<in> set [1392..<1408]" unfolding set_upt by simp
  then have "j \<in> set [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]" unfolding gupt_nc_087 .
  then show "goc_sub None j" using goc_nc_1392 goc_nc_1393 goc_nc_1394 goc_nc_1395 goc_nc_1396 goc_nc_1397 goc_nc_1398 goc_nc_1399 goc_nc_1400 goc_nc_1401 goc_nc_1402 goc_nc_1403 goc_nc_1404 goc_nc_1405 goc_nc_1406 goc_nc_1407
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
