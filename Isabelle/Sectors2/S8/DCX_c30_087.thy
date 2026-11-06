theory DCX_c30_087
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1392: "dc_sub dc_b30 1392"
  by (dc_eval dc_c30_1392)

lemma dc_c30_1393: "dc_sub dc_b30 1393"
  by (dc_eval dc_c30_1393)

lemma dc_c30_1394: "dc_sub dc_b30 1394"
  by (dc_eval dc_c30_1394)

lemma dc_c30_1395: "dc_sub dc_b30 1395"
  by (dc_eval dc_c30_1395)

lemma dc_c30_1396: "dc_sub dc_b30 1396"
  by (dc_eval dc_c30_1396)

lemma dc_c30_1397: "dc_sub dc_b30 1397"
  by (dc_eval dc_c30_1397)

lemma dc_c30_1398: "dc_sub dc_b30 1398"
  by (dc_eval dc_c30_1398)

lemma dc_c30_1399: "dc_sub dc_b30 1399"
  by (dc_eval dc_c30_1399)

lemma dc_c30_1400: "dc_sub dc_b30 1400"
  by (dc_eval dc_c30_1400)

lemma dc_c30_1401: "dc_sub dc_b30 1401"
  by (dc_eval dc_c30_1401)

lemma dc_c30_1402: "dc_sub dc_b30 1402"
  by (dc_eval dc_c30_1402)

lemma dc_c30_1403: "dc_sub dc_b30 1403"
  by (dc_eval dc_c30_1403)

lemma dc_c30_1404: "dc_sub dc_b30 1404"
  by (dc_eval dc_c30_1404)

lemma dc_c30_1405: "dc_sub dc_b30 1405"
  by (dc_eval dc_c30_1405)

lemma dc_c30_1406: "dc_sub dc_b30 1406"
  by (dc_eval dc_c30_1406)

lemma dc_c30_1407: "dc_sub dc_b30 1407"
  by (dc_eval dc_c30_1407)

lemma upt_c30_087: "[1392..<1408] = [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]"
  by (simp add: upt_rec)

lemma sec_c30_087: "\<forall>j\<in>{16 * 87..<16 * 87 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 87..<16 * 87 + 16}"
  then have "j \<in> set [1392..<1408]" unfolding set_upt by simp
  then have "j \<in> set [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]" unfolding upt_c30_087 .
  then show "dc_sub dc_b30 j" using dc_c30_1392 dc_c30_1393 dc_c30_1394 dc_c30_1395 dc_c30_1396 dc_c30_1397 dc_c30_1398 dc_c30_1399 dc_c30_1400 dc_c30_1401 dc_c30_1402 dc_c30_1403 dc_c30_1404 dc_c30_1405 dc_c30_1406 dc_c30_1407
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
