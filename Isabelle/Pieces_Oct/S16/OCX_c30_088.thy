theory OCX_c30_088
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1408: "oc_sub oc_b30 1408"
  by (oc_eval oc_c30_1408)

lemma oc_c30_1409: "oc_sub oc_b30 1409"
  by (oc_eval oc_c30_1409)

lemma oc_c30_1410: "oc_sub oc_b30 1410"
  by (oc_eval oc_c30_1410)

lemma oc_c30_1411: "oc_sub oc_b30 1411"
  by (oc_eval oc_c30_1411)

lemma oc_c30_1412: "oc_sub oc_b30 1412"
  by (oc_eval oc_c30_1412)

lemma oc_c30_1413: "oc_sub oc_b30 1413"
  by (oc_eval oc_c30_1413)

lemma oc_c30_1414: "oc_sub oc_b30 1414"
  by (oc_eval oc_c30_1414)

lemma oc_c30_1415: "oc_sub oc_b30 1415"
  by (oc_eval oc_c30_1415)

lemma oc_c30_1416: "oc_sub oc_b30 1416"
  by (oc_eval oc_c30_1416)

lemma oc_c30_1417: "oc_sub oc_b30 1417"
  by (oc_eval oc_c30_1417)

lemma oc_c30_1418: "oc_sub oc_b30 1418"
  by (oc_eval oc_c30_1418)

lemma oc_c30_1419: "oc_sub oc_b30 1419"
  by (oc_eval oc_c30_1419)

lemma oc_c30_1420: "oc_sub oc_b30 1420"
  by (oc_eval oc_c30_1420)

lemma oc_c30_1421: "oc_sub oc_b30 1421"
  by (oc_eval oc_c30_1421)

lemma oc_c30_1422: "oc_sub oc_b30 1422"
  by (oc_eval oc_c30_1422)

lemma oc_c30_1423: "oc_sub oc_b30 1423"
  by (oc_eval oc_c30_1423)

lemma upt_c30_088: "[1408..<1424] = [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]"
  by (simp add: upt_rec)

lemma sec_c30_088: "\<forall>j\<in>{16 * 88..<16 * 88 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 88..<16 * 88 + 16}"
  then have "j \<in> set [1408..<1424]" unfolding set_upt by simp
  then have "j \<in> set [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]" unfolding upt_c30_088 .
  then show "oc_sub oc_b30 j" using oc_c30_1408 oc_c30_1409 oc_c30_1410 oc_c30_1411 oc_c30_1412 oc_c30_1413 oc_c30_1414 oc_c30_1415 oc_c30_1416 oc_c30_1417 oc_c30_1418 oc_c30_1419 oc_c30_1420 oc_c30_1421 oc_c30_1422 oc_c30_1423
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
