theory OCX_nc_088
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1408: "oc_sub None 1408"
  by (oc_eval oc_nc_1408)

lemma oc_nc_1409: "oc_sub None 1409"
  by (oc_eval oc_nc_1409)

lemma oc_nc_1410: "oc_sub None 1410"
  by (oc_eval oc_nc_1410)

lemma oc_nc_1411: "oc_sub None 1411"
  by (oc_eval oc_nc_1411)

lemma oc_nc_1412: "oc_sub None 1412"
  by (oc_eval oc_nc_1412)

lemma oc_nc_1413: "oc_sub None 1413"
  by (oc_eval oc_nc_1413)

lemma oc_nc_1414: "oc_sub None 1414"
  by (oc_eval oc_nc_1414)

lemma oc_nc_1415: "oc_sub None 1415"
  by (oc_eval oc_nc_1415)

lemma oc_nc_1416: "oc_sub None 1416"
  by (oc_eval oc_nc_1416)

lemma oc_nc_1417: "oc_sub None 1417"
  by (oc_eval oc_nc_1417)

lemma oc_nc_1418: "oc_sub None 1418"
  by (oc_eval oc_nc_1418)

lemma oc_nc_1419: "oc_sub None 1419"
  by (oc_eval oc_nc_1419)

lemma oc_nc_1420: "oc_sub None 1420"
  by (oc_eval oc_nc_1420)

lemma oc_nc_1421: "oc_sub None 1421"
  by (oc_eval oc_nc_1421)

lemma oc_nc_1422: "oc_sub None 1422"
  by (oc_eval oc_nc_1422)

lemma oc_nc_1423: "oc_sub None 1423"
  by (oc_eval oc_nc_1423)

lemma upt_nc_088: "[1408..<1424] = [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]"
  by (simp add: upt_rec)

lemma sec_nc_088: "\<forall>j\<in>{16 * 88..<16 * 88 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 88..<16 * 88 + 16}"
  then have "j \<in> set [1408..<1424]" unfolding set_upt by simp
  then have "j \<in> set [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]" unfolding upt_nc_088 .
  then show "oc_sub None j" using oc_nc_1408 oc_nc_1409 oc_nc_1410 oc_nc_1411 oc_nc_1412 oc_nc_1413 oc_nc_1414 oc_nc_1415 oc_nc_1416 oc_nc_1417 oc_nc_1418 oc_nc_1419 oc_nc_1420 oc_nc_1421 oc_nc_1422 oc_nc_1423
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
