theory DCX_nc_088
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1408: "dc_sub None 1408"
  by (dc_eval dc_nc_1408)

lemma dc_nc_1409: "dc_sub None 1409"
  by (dc_eval dc_nc_1409)

lemma dc_nc_1410: "dc_sub None 1410"
  by (dc_eval dc_nc_1410)

lemma dc_nc_1411: "dc_sub None 1411"
  by (dc_eval dc_nc_1411)

lemma dc_nc_1412: "dc_sub None 1412"
  by (dc_eval dc_nc_1412)

lemma dc_nc_1413: "dc_sub None 1413"
  by (dc_eval dc_nc_1413)

lemma dc_nc_1414: "dc_sub None 1414"
  by (dc_eval dc_nc_1414)

lemma dc_nc_1415: "dc_sub None 1415"
  by (dc_eval dc_nc_1415)

lemma dc_nc_1416: "dc_sub None 1416"
  by (dc_eval dc_nc_1416)

lemma dc_nc_1417: "dc_sub None 1417"
  by (dc_eval dc_nc_1417)

lemma dc_nc_1418: "dc_sub None 1418"
  by (dc_eval dc_nc_1418)

lemma dc_nc_1419: "dc_sub None 1419"
  by (dc_eval dc_nc_1419)

lemma dc_nc_1420: "dc_sub None 1420"
  by (dc_eval dc_nc_1420)

lemma dc_nc_1421: "dc_sub None 1421"
  by (dc_eval dc_nc_1421)

lemma dc_nc_1422: "dc_sub None 1422"
  by (dc_eval dc_nc_1422)

lemma dc_nc_1423: "dc_sub None 1423"
  by (dc_eval dc_nc_1423)

lemma upt_nc_088: "[1408..<1424] = [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]"
  by (simp add: upt_rec)

lemma sec_nc_088: "\<forall>j\<in>{16 * 88..<16 * 88 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 88..<16 * 88 + 16}"
  then have "j \<in> set [1408..<1424]" unfolding set_upt by simp
  then have "j \<in> set [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]" unfolding upt_nc_088 .
  then show "dc_sub None j" using dc_nc_1408 dc_nc_1409 dc_nc_1410 dc_nc_1411 dc_nc_1412 dc_nc_1413 dc_nc_1414 dc_nc_1415 dc_nc_1416 dc_nc_1417 dc_nc_1418 dc_nc_1419 dc_nc_1420 dc_nc_1421 dc_nc_1422 dc_nc_1423
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
