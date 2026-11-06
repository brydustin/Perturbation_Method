theory GDCX_nc_092
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1472: "gdc_sub None 1472"
  by (gdc_eval gdc_nc_1472)

lemma gdc_nc_1473: "gdc_sub None 1473"
  by (gdc_eval gdc_nc_1473)

lemma gdc_nc_1474: "gdc_sub None 1474"
  by (gdc_eval gdc_nc_1474)

lemma gdc_nc_1475: "gdc_sub None 1475"
  by (gdc_eval gdc_nc_1475)

lemma gdc_nc_1476: "gdc_sub None 1476"
  by (gdc_eval gdc_nc_1476)

lemma gdc_nc_1477: "gdc_sub None 1477"
  by (gdc_eval gdc_nc_1477)

lemma gdc_nc_1478: "gdc_sub None 1478"
  by (gdc_eval gdc_nc_1478)

lemma gdc_nc_1479: "gdc_sub None 1479"
  by (gdc_eval gdc_nc_1479)

lemma gdc_nc_1480: "gdc_sub None 1480"
  by (gdc_eval gdc_nc_1480)

lemma gdc_nc_1481: "gdc_sub None 1481"
  by (gdc_eval gdc_nc_1481)

lemma gdc_nc_1482: "gdc_sub None 1482"
  by (gdc_eval gdc_nc_1482)

lemma gdc_nc_1483: "gdc_sub None 1483"
  by (gdc_eval gdc_nc_1483)

lemma gdc_nc_1484: "gdc_sub None 1484"
  by (gdc_eval gdc_nc_1484)

lemma gdc_nc_1485: "gdc_sub None 1485"
  by (gdc_eval gdc_nc_1485)

lemma gdc_nc_1486: "gdc_sub None 1486"
  by (gdc_eval gdc_nc_1486)

lemma gdc_nc_1487: "gdc_sub None 1487"
  by (gdc_eval gdc_nc_1487)

lemma gupt_nc_092: "[1472..<1488] = [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]"
  by (simp add: upt_rec)

lemma gsec_nc_092: "\<forall>j\<in>{16 * 92..<16 * 92 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 92..<16 * 92 + 16}"
  then have "j \<in> set [1472..<1488]" unfolding set_upt by simp
  then have "j \<in> set [1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487]" unfolding gupt_nc_092 .
  then show "gdc_sub None j" using gdc_nc_1472 gdc_nc_1473 gdc_nc_1474 gdc_nc_1475 gdc_nc_1476 gdc_nc_1477 gdc_nc_1478 gdc_nc_1479 gdc_nc_1480 gdc_nc_1481 gdc_nc_1482 gdc_nc_1483 gdc_nc_1484 gdc_nc_1485 gdc_nc_1486 gdc_nc_1487
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
