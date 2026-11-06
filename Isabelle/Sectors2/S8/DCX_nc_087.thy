theory DCX_nc_087
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1392: "dc_sub None 1392"
  by (dc_eval dc_nc_1392)

lemma dc_nc_1393: "dc_sub None 1393"
  by (dc_eval dc_nc_1393)

lemma dc_nc_1394: "dc_sub None 1394"
  by (dc_eval dc_nc_1394)

lemma dc_nc_1395: "dc_sub None 1395"
  by (dc_eval dc_nc_1395)

lemma dc_nc_1396: "dc_sub None 1396"
  by (dc_eval dc_nc_1396)

lemma dc_nc_1397: "dc_sub None 1397"
  by (dc_eval dc_nc_1397)

lemma dc_nc_1398: "dc_sub None 1398"
  by (dc_eval dc_nc_1398)

lemma dc_nc_1399: "dc_sub None 1399"
  by (dc_eval dc_nc_1399)

lemma dc_nc_1400: "dc_sub None 1400"
  by (dc_eval dc_nc_1400)

lemma dc_nc_1401: "dc_sub None 1401"
  by (dc_eval dc_nc_1401)

lemma dc_nc_1402: "dc_sub None 1402"
  by (dc_eval dc_nc_1402)

lemma dc_nc_1403: "dc_sub None 1403"
  by (dc_eval dc_nc_1403)

lemma dc_nc_1404: "dc_sub None 1404"
  by (dc_eval dc_nc_1404)

lemma dc_nc_1405: "dc_sub None 1405"
  by (dc_eval dc_nc_1405)

lemma dc_nc_1406: "dc_sub None 1406"
  by (dc_eval dc_nc_1406)

lemma dc_nc_1407: "dc_sub None 1407"
  by (dc_eval dc_nc_1407)

lemma upt_nc_087: "[1392..<1408] = [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]"
  by (simp add: upt_rec)

lemma sec_nc_087: "\<forall>j\<in>{16 * 87..<16 * 87 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 87..<16 * 87 + 16}"
  then have "j \<in> set [1392..<1408]" unfolding set_upt by simp
  then have "j \<in> set [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]" unfolding upt_nc_087 .
  then show "dc_sub None j" using dc_nc_1392 dc_nc_1393 dc_nc_1394 dc_nc_1395 dc_nc_1396 dc_nc_1397 dc_nc_1398 dc_nc_1399 dc_nc_1400 dc_nc_1401 dc_nc_1402 dc_nc_1403 dc_nc_1404 dc_nc_1405 dc_nc_1406 dc_nc_1407
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
