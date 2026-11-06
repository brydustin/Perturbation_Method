theory GDCX_nc_088
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1408: "gdc_sub None 1408"
  by (gdc_eval gdc_nc_1408)

lemma gdc_nc_1409: "gdc_sub None 1409"
  by (gdc_eval gdc_nc_1409)

lemma gdc_nc_1410: "gdc_sub None 1410"
  by (gdc_eval gdc_nc_1410)

lemma gdc_nc_1411: "gdc_sub None 1411"
  by (gdc_eval gdc_nc_1411)

lemma gdc_nc_1412: "gdc_sub None 1412"
  by (gdc_eval gdc_nc_1412)

lemma gdc_nc_1413: "gdc_sub None 1413"
  by (gdc_eval gdc_nc_1413)

lemma gdc_nc_1414: "gdc_sub None 1414"
  by (gdc_eval gdc_nc_1414)

lemma gdc_nc_1415: "gdc_sub None 1415"
  by (gdc_eval gdc_nc_1415)

lemma gdc_nc_1416: "gdc_sub None 1416"
  by (gdc_eval gdc_nc_1416)

lemma gdc_nc_1417: "gdc_sub None 1417"
  by (gdc_eval gdc_nc_1417)

lemma gdc_nc_1418: "gdc_sub None 1418"
  by (gdc_eval gdc_nc_1418)

lemma gdc_nc_1419: "gdc_sub None 1419"
  by (gdc_eval gdc_nc_1419)

lemma gdc_nc_1420: "gdc_sub None 1420"
  by (gdc_eval gdc_nc_1420)

lemma gdc_nc_1421: "gdc_sub None 1421"
  by (gdc_eval gdc_nc_1421)

lemma gdc_nc_1422: "gdc_sub None 1422"
  by (gdc_eval gdc_nc_1422)

lemma gdc_nc_1423: "gdc_sub None 1423"
  by (gdc_eval gdc_nc_1423)

lemma gupt_nc_088: "[1408..<1424] = [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]"
  by (simp add: upt_rec)

lemma gsec_nc_088: "\<forall>j\<in>{16 * 88..<16 * 88 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 88..<16 * 88 + 16}"
  then have "j \<in> set [1408..<1424]" unfolding set_upt by simp
  then have "j \<in> set [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]" unfolding gupt_nc_088 .
  then show "gdc_sub None j" using gdc_nc_1408 gdc_nc_1409 gdc_nc_1410 gdc_nc_1411 gdc_nc_1412 gdc_nc_1413 gdc_nc_1414 gdc_nc_1415 gdc_nc_1416 gdc_nc_1417 gdc_nc_1418 gdc_nc_1419 gdc_nc_1420 gdc_nc_1421 gdc_nc_1422 gdc_nc_1423
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
