theory OCX_c30_087
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1392: "oc_sub oc_b30 1392"
  by (oc_eval oc_c30_1392)

lemma oc_c30_1393: "oc_sub oc_b30 1393"
  by (oc_eval oc_c30_1393)

lemma oc_c30_1394: "oc_sub oc_b30 1394"
  by (oc_eval oc_c30_1394)

lemma oc_c30_1395: "oc_sub oc_b30 1395"
  by (oc_eval oc_c30_1395)

lemma oc_c30_1396: "oc_sub oc_b30 1396"
  by (oc_eval oc_c30_1396)

lemma oc_c30_1397: "oc_sub oc_b30 1397"
  by (oc_eval oc_c30_1397)

lemma oc_c30_1398: "oc_sub oc_b30 1398"
  by (oc_eval oc_c30_1398)

lemma oc_c30_1399: "oc_sub oc_b30 1399"
  by (oc_eval oc_c30_1399)

lemma oc_c30_1400: "oc_sub oc_b30 1400"
  by (oc_eval oc_c30_1400)

lemma oc_c30_1401: "oc_sub oc_b30 1401"
  by (oc_eval oc_c30_1401)

lemma oc_c30_1402: "oc_sub oc_b30 1402"
  by (oc_eval oc_c30_1402)

lemma oc_c30_1403: "oc_sub oc_b30 1403"
  by (oc_eval oc_c30_1403)

lemma oc_c30_1404: "oc_sub oc_b30 1404"
  by (oc_eval oc_c30_1404)

lemma oc_c30_1405: "oc_sub oc_b30 1405"
  by (oc_eval oc_c30_1405)

lemma oc_c30_1406: "oc_sub oc_b30 1406"
  by (oc_eval oc_c30_1406)

lemma oc_c30_1407: "oc_sub oc_b30 1407"
  by (oc_eval oc_c30_1407)

lemma upt_c30_087: "[1392..<1408] = [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]"
  by (simp add: upt_rec)

lemma sec_c30_087: "\<forall>j\<in>{16 * 87..<16 * 87 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 87..<16 * 87 + 16}"
  then have "j \<in> set [1392..<1408]" unfolding set_upt by simp
  then have "j \<in> set [1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407]" unfolding upt_c30_087 .
  then show "oc_sub oc_b30 j" using oc_c30_1392 oc_c30_1393 oc_c30_1394 oc_c30_1395 oc_c30_1396 oc_c30_1397 oc_c30_1398 oc_c30_1399 oc_c30_1400 oc_c30_1401 oc_c30_1402 oc_c30_1403 oc_c30_1404 oc_c30_1405 oc_c30_1406 oc_c30_1407
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
