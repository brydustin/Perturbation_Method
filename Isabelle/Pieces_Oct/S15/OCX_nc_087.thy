theory OCX_nc_087
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1392: "oc_sub None 1392"
  by (oc_eval oc_nc_1392)

lemma oc_nc_1393: "oc_sub None 1393"
  by (oc_eval oc_nc_1393)

lemma oc_nc_1394: "oc_sub None 1394"
  by (oc_eval oc_nc_1394)

lemma oc_nc_1395: "oc_sub None 1395"
  by (oc_eval oc_nc_1395)

lemma oc_nc_1396: "oc_sub None 1396"
  by (oc_eval oc_nc_1396)

lemma oc_nc_1397: "oc_sub None 1397"
  by (oc_eval oc_nc_1397)

lemma oc_nc_1398: "oc_sub None 1398"
  by (oc_eval oc_nc_1398)

lemma oc_nc_1399: "oc_sub None 1399"
  by (oc_eval oc_nc_1399)

lemma oc_nc_1400: "oc_sub None 1400"
  by (oc_eval oc_nc_1400)

lemma oc_nc_1401: "oc_sub None 1401"
  by (oc_eval oc_nc_1401)

lemma oc_nc_1402: "oc_sub None 1402"
  by (oc_eval oc_nc_1402)

lemma oc_nc_1403: "oc_sub None 1403"
  by (oc_eval oc_nc_1403)

lemma oc_nc_1404: "oc_sub None 1404"
  by (oc_eval oc_nc_1404)

lemma oc_nc_1405: "oc_sub None 1405"
  by (oc_eval oc_nc_1405)

lemma oc_nc_1406: "oc_sub None 1406"
  by (oc_eval oc_nc_1406)

lemma oc_nc_1407: "oc_sub None 1407"
  by (oc_eval oc_nc_1407)

lemma upt_nc_087: "[1392..<1408] = [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]"
  by (simp add: upt_rec)

lemma sec_nc_087: "\<forall>j\<in>{16 * 87..<16 * 87 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 87..<16 * 87 + 16}"
  then have "j \<in> set [1392..<1408]" unfolding set_upt by simp
  then have "j \<in> set [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]" unfolding upt_nc_087 .
  then show "oc_sub None j" using oc_nc_1392 oc_nc_1393 oc_nc_1394 oc_nc_1395 oc_nc_1396 oc_nc_1397 oc_nc_1398 oc_nc_1399 oc_nc_1400 oc_nc_1401 oc_nc_1402 oc_nc_1403 oc_nc_1404 oc_nc_1405 oc_nc_1406 oc_nc_1407
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
