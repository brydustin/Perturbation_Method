theory GOCX_nc_088
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1408: "goc_sub None 1408"
  by (goc_eval goc_nc_1408)

lemma goc_nc_1409: "goc_sub None 1409"
  by (goc_eval goc_nc_1409)

lemma goc_nc_1410: "goc_sub None 1410"
  by (goc_eval goc_nc_1410)

lemma goc_nc_1411: "goc_sub None 1411"
  by (goc_eval goc_nc_1411)

lemma goc_nc_1412: "goc_sub None 1412"
  by (goc_eval goc_nc_1412)

lemma goc_nc_1413: "goc_sub None 1413"
  by (goc_eval goc_nc_1413)

lemma goc_nc_1414: "goc_sub None 1414"
  by (goc_eval goc_nc_1414)

lemma goc_nc_1415: "goc_sub None 1415"
  by (goc_eval goc_nc_1415)

lemma goc_nc_1416: "goc_sub None 1416"
  by (goc_eval goc_nc_1416)

lemma goc_nc_1417: "goc_sub None 1417"
  by (goc_eval goc_nc_1417)

lemma goc_nc_1418: "goc_sub None 1418"
  by (goc_eval goc_nc_1418)

lemma goc_nc_1419: "goc_sub None 1419"
  by (goc_eval goc_nc_1419)

lemma goc_nc_1420: "goc_sub None 1420"
  by (goc_eval goc_nc_1420)

lemma goc_nc_1421: "goc_sub None 1421"
  by (goc_eval goc_nc_1421)

lemma goc_nc_1422: "goc_sub None 1422"
  by (goc_eval goc_nc_1422)

lemma goc_nc_1423: "goc_sub None 1423"
  by (goc_eval goc_nc_1423)

lemma gupt_nc_088: "[1408..<1424] = [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]"
  by (simp add: upt_rec)

lemma gsec_nc_088: "\<forall>j\<in>{16 * 88..<16 * 88 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 88..<16 * 88 + 16}"
  then have "j \<in> set [1408..<1424]" unfolding set_upt by simp
  then have "j \<in> set [1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423]" unfolding gupt_nc_088 .
  then show "goc_sub None j" using goc_nc_1408 goc_nc_1409 goc_nc_1410 goc_nc_1411 goc_nc_1412 goc_nc_1413 goc_nc_1414 goc_nc_1415 goc_nc_1416 goc_nc_1417 goc_nc_1418 goc_nc_1419 goc_nc_1420 goc_nc_1421 goc_nc_1422 goc_nc_1423
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
