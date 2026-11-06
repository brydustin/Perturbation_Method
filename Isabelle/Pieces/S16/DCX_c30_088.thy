theory DCX_c30_088
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1408: "dc_sub dc_b30 1408"
  by (dc_eval dc_c30_1408)

lemma dc_c30_1409: "dc_sub dc_b30 1409"
  by (dc_eval dc_c30_1409)

lemma dc_c30_1410: "dc_sub dc_b30 1410"
  by (dc_eval dc_c30_1410)

lemma dc_c30_1411: "dc_sub dc_b30 1411"
  by (dc_eval dc_c30_1411)

lemma dc_c30_1412: "dc_sub dc_b30 1412"
  by (dc_eval dc_c30_1412)

lemma dc_c30_1413: "dc_sub dc_b30 1413"
  by (dc_eval dc_c30_1413)

lemma dc_c30_1414: "dc_sub dc_b30 1414"
  by (dc_eval dc_c30_1414)

lemma dc_c30_1415: "dc_sub dc_b30 1415"
  by (dc_eval dc_c30_1415)

lemma dc_c30_1416: "dc_sub dc_b30 1416"
  by (dc_eval dc_c30_1416)

lemma dc_c30_1417: "dc_sub dc_b30 1417"
  by (dc_eval dc_c30_1417)

lemma dc_c30_1418: "dc_sub dc_b30 1418"
  by (dc_eval dc_c30_1418)

lemma dc_c30_1419: "dc_sub dc_b30 1419"
  by (dc_eval dc_c30_1419)

lemma dc_c30_1420: "dc_sub dc_b30 1420"
  by (dc_eval dc_c30_1420)

lemma dc_c30_1421: "dc_sub dc_b30 1421"
  by (dc_eval dc_c30_1421)

lemma dc_c30_1422: "dc_sub dc_b30 1422"
  by (dc_eval dc_c30_1422)

lemma dc_c30_1423: "dc_sub dc_b30 1423"
  by (dc_eval dc_c30_1423)

lemma upt_c30_088: "[1408..<1424] = [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]"
  by (simp add: upt_rec)

lemma sec_c30_088: "\<forall>j\<in>{16 * 88..<16 * 88 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 88..<16 * 88 + 16}"
  then have "j \<in> set [1408..<1424]" unfolding set_upt by simp
  then have "j \<in> set [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]" unfolding upt_c30_088 .
  then show "dc_sub dc_b30 j" using dc_c30_1408 dc_c30_1409 dc_c30_1410 dc_c30_1411 dc_c30_1412 dc_c30_1413 dc_c30_1414 dc_c30_1415 dc_c30_1416 dc_c30_1417 dc_c30_1418 dc_c30_1419 dc_c30_1420 dc_c30_1421 dc_c30_1422 dc_c30_1423
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
